// ==================== GLOBAL STATE ====================
        const canvas = document.getElementById('graphCanvas');
        const ctx = canvas.getContext('2d');
        const nodeLabelsDiv = document.getElementById('node-labels');
        
        const NODE_RADIUS = 10;
        const NODE_COLOR = '#4b5563';
        const EDGE_COLOR = '#9ca3af';
        const WEIGHT_COLOR = '#374151';
        const HIGHLIGHT_VISITED = '#f97316';
        const HIGHLIGHT_CURRENT = '#ef4444';
        const HIGHLIGHT_PATH = '#3b82f6';
        
        let GRAPH_DATA = {};
        let NODE_NAMES = [];
        let nextNodeId = 65; // 'A'
        let currentMode = 'ADD_NODE';
        
        let isDrawingEdge = false;
        let startNodeForEdge = null;
        let currentEdgeX = 0;
        let currentEdgeY = 0;
        
        let ALGORITHM_HISTORY = [];
        let CURRENT_STEP = 0;
        let IS_RUNNING = false;
        let START_TIME = 0;
        let END_TIME = 0;
        let FINAL_PATH = null;
        let OPERATION_COUNT = 0;
        
        let AUTO_PLAY = false;
        let AUTO_PLAY_INTERVAL = null;

        // ==================== HELPER CLASSES ====================
        class MinPriorityQueue {
            constructor() { this.values = []; }
            enqueue(element) {
                this.values.push(element);
                this.bubbleUp(this.values.length - 1);
            }
            dequeue() {
                if (this.values.length === 0) return null;
                if (this.values.length === 1) return this.values.pop();
                [this.values[0], this.values[this.values.length - 1]] = [this.values[this.values.length - 1], this.values[0]];
                const min = this.values.pop();
                this.sinkDown(0);
                return min;
            }
            size() { return this.values.length; }
            getComparisonValue(element) { return element.distance !== undefined ? element.distance : element.weight; }
            bubbleUp(idx) {
                let element = this.values[idx];
                let elementValue = this.getComparisonValue(element);
                while(idx > 0) {
                    let parentIdx = Math.floor((idx - 1) / 2);
                    let parent = this.values[parentIdx];
                    let parentValue = this.getComparisonValue(parent);
                    if(elementValue >= parentValue) break;
                    this.values[parentIdx] = element;
                    this.values[idx] = parent;
                    idx = parentIdx;
                }
            }
            sinkDown(idx) {
                const length = this.values.length;
                const element = this.values[idx];
                const elementValue = this.getComparisonValue(element);
                while(true) {
                    let leftChildIdx = 2 * idx + 1;
                    let rightChildIdx = 2 * idx + 2;
                    let leftChild, rightChild;
                    let leftChildValue, rightChildValue;
                    let swap = null;
                    if (leftChildIdx < length) {
                        leftChild = this.values[leftChildIdx];
                        leftChildValue = this.getComparisonValue(leftChild);
                        if (leftChildValue < elementValue) swap = leftChildIdx;
                    }
                    if (rightChildIdx < length) {
                        rightChild = this.values[rightChildIdx];
                        rightChildValue = this.getComparisonValue(rightChild);
                        if ((swap === null && rightChildValue < elementValue) || (swap !== null && rightChildValue < leftChildValue)) {
                            swap = rightChildIdx;
                        }
                    }
                    if (swap === null) break;
                    [this.values[idx], this.values[swap]] = [this.values[swap], this.values[idx]];
                    idx = swap;
                }
            }
        }
        
        class DisjointSet {
            constructor(nodes) {
                this.parent = {};
                this.rank = {};
                nodes.forEach(node => {
                    this.parent[node] = node;
                    this.rank[node] = 0;
                });
            }
            find(node) {
                if (this.parent[node] === node) return node;
                this.parent[node] = this.find(this.parent[node]);
                return this.parent[node];
            }
            union(node1, node2) {
                const root1 = this.find(node1);
                const root2 = this.find(node2);
                if (root1 !== root2) {
                    if (this.rank[root1] < this.rank[root2]) {
                        this.parent[root1] = root2;
                    } else if (this.rank[root1] > this.rank[root2]) {
                        this.parent[root2] = root1;
                    } else {
                        this.parent[root2] = root1;
                        this.rank[root1]++;
                    }
                    return true;
                }
                return false;
            }
        }

        // ==================== CANVAS SETUP ====================
        function initializeCanvas() {
            const container = document.getElementById('canvas-container');
            const width = container.clientWidth;
            canvas.width = width;
            canvas.height = Math.max(400, width * 0.6);
            drawGraph();
            updateComplexityDisplay();
            updateGraphMetrics();
        }

        function drawArrowhead(ctx, fromX, fromY, toX, toY, nodeRadius) {
            const headlen = 12;
            const angle = Math.atan2(toY - fromY, toX - fromX);
            const arrowEndX = toX - nodeRadius * Math.cos(angle);
            const arrowEndY = toY - nodeRadius * Math.sin(angle);
            ctx.beginPath();
            ctx.moveTo(arrowEndX, arrowEndY);
            ctx.lineTo(arrowEndX - headlen * Math.cos(angle - Math.PI / 6), arrowEndY - headlen * Math.sin(angle - Math.PI / 6));
            ctx.lineTo(arrowEndX - headlen * Math.cos(angle + Math.PI / 6), arrowEndY - headlen * Math.sin(angle + Math.PI / 6));
            ctx.lineTo(arrowEndX, arrowEndY);
            ctx.fillStyle = ctx.strokeStyle;
            ctx.fill();
        }

        function getCanvasCoordinates(event) {
            const rect = canvas.getBoundingClientRect();
            const x = (event.clientX - rect.left) / rect.width * canvas.width;
            const y = (event.clientY - rect.top) / rect.height * canvas.height;
            return { x, y };
        }

        function getNodeAt(x, y) {
            for (const nodeKey of NODE_NAMES) {
                const node = GRAPH_DATA[nodeKey];
                if (node && Math.hypot(node.x - x, node.y - y) < NODE_RADIUS) {
                    return nodeKey;
                }
            }
            return null;
        }

        function drawGraph(highlightedNodes = new Set(), highlightedEdges = new Set(), finalPath = new Set(), mstCost = null) {
            ctx.clearRect(0, 0, canvas.width, canvas.height);
            nodeLabelsDiv.innerHTML = '';
            const isDirected = document.getElementById('directed-toggle').checked;

            // Draw edges
            for (const nodeKey of NODE_NAMES) {
                const node = GRAPH_DATA[nodeKey];
                if (!node || !node.neighbors) continue;
                
                for (const neighbor of node.neighbors) {
                    const neighborData = GRAPH_DATA[neighbor.node];
                    if (!neighborData) continue;
                    
                    let drawThisWay = true;
                    if (!isDirected && nodeKey > neighbor.node) drawThisWay = false;
                    
                    if (drawThisWay) {
                        const edgeKey = isDirected ? `${nodeKey}-${neighbor.node}` : (nodeKey < neighbor.node ? `${nodeKey}-${neighbor.node}` : `${neighbor.node}-${nodeKey}`);
                        const isPath = finalPath.has(edgeKey);
                        const isHighlighted = highlightedEdges.has(edgeKey);

                        ctx.beginPath();
                        ctx.moveTo(node.x, node.y);
                        ctx.lineTo(neighborData.x, neighborData.y);
                        ctx.lineWidth = isPath ? 4 : 3;
                        ctx.strokeStyle = isPath ? HIGHLIGHT_PATH : (isHighlighted ? HIGHLIGHT_VISITED : EDGE_COLOR);
                        ctx.stroke();

                        if (isDirected) {
                            drawArrowhead(ctx, node.x, node.y, neighborData.x, neighborData.y, NODE_RADIUS);
                        }
                        
                        const midX = (node.x + neighborData.x) / 2;
                        const midY = (node.y + neighborData.y) / 2;
                        ctx.fillStyle = isPath ? HIGHLIGHT_PATH : (isHighlighted ? HIGHLIGHT_VISITED : WEIGHT_COLOR);
                        ctx.font = 'bold 13px Inter';
                        ctx.textAlign = 'center';
                        ctx.fillText(neighbor.weight, midX + 12, midY - 5);
                    }
                }
            }

            // Draw temporary edge
            if (isDrawingEdge && startNodeForEdge && currentMode === 'ADD_EDGE') {
                const startNode = GRAPH_DATA[startNodeForEdge];
                ctx.beginPath();
                ctx.moveTo(startNode.x, startNode.y);
                ctx.lineTo(currentEdgeX, currentEdgeY);
                ctx.lineWidth = 2;
                ctx.strokeStyle = HIGHLIGHT_PATH;
                ctx.setLineDash([5, 5]);
                ctx.stroke();
                ctx.setLineDash([]);
                if (isDirected) {
                    drawArrowhead(ctx, startNode.x, startNode.y, currentEdgeX, currentEdgeY, 0);
                }
            }

            // Draw nodes
            for (const nodeKey of NODE_NAMES) {
                const node = GRAPH_DATA[nodeKey];
                if (!node) continue;
                
                let color = NODE_COLOR;
                const isCurrentProcessingNode = ALGORITHM_HISTORY[CURRENT_STEP - 1] && nodeKey === ALGORITHM_HISTORY[CURRENT_STEP - 1].node;

                if (highlightedNodes.has(nodeKey)) {
                    color = isCurrentProcessingNode ? HIGHLIGHT_CURRENT : HIGHLIGHT_VISITED;
                }
                if (finalPath.has(nodeKey)) {
                    color = HIGHLIGHT_PATH;
                }
                if (currentMode === 'ADD_EDGE' && startNodeForEdge === nodeKey) {
                    color = HIGHLIGHT_CURRENT;
                }
                if (currentMode === 'DELETE') {
                    color = '#ef4444';
                }

                ctx.beginPath();
                ctx.arc(node.x, node.y, NODE_RADIUS, 0, 2 * Math.PI);
                ctx.fillStyle = color;
                ctx.fill();
                ctx.strokeStyle = '#1f2937';
                ctx.lineWidth = 2;
                ctx.stroke();

                const label = document.createElement('div');
                label.className = 'node-label';
                label.textContent = nodeKey;
                label.style.color = (color === NODE_COLOR) ? '#1f2937' : 'white';
                
                const canvasRect = canvas.getBoundingClientRect();
                const scaleX = canvasRect.width / canvas.width;
                const scaleY = canvasRect.height / canvas.height;
                
                label.style.left = (node.x * scaleX) + 'px';
                label.style.top = (node.y * scaleY) + 'px';
                
                nodeLabelsDiv.appendChild(label);
            }

            if (mstCost !== null) {
                ctx.fillStyle = HIGHLIGHT_PATH;
                ctx.font = 'bold 20px Inter';
                ctx.textAlign = 'right';
                ctx.fillText(`MST Cost: ${mstCost.toFixed(2)}`, canvas.width - 20, 30);
            }
        }

        // ==================== GRAPH INTERACTION ====================
        function setMode(mode) {
            currentMode = mode;
            isDrawingEdge = false;
            startNodeForEdge = null;
            
            document.getElementById('mode-node-btn').classList.remove('mode-button-active');
            document.getElementById('mode-edge-btn').classList.remove('mode-button-active');
            document.getElementById('mode-delete-btn').classList.remove('mode-button-active');
            
            if (mode === 'ADD_NODE') {
                document.getElementById('mode-node-btn').classList.add('mode-button-active');
                document.getElementById('current-mode-display').textContent = 'Add Node';
                document.getElementById('graph-interaction-status').textContent = 'Click canvas to add nodes';
                canvas.style.cursor = 'crosshair';
            } else if (mode === 'ADD_EDGE') {
                document.getElementById('mode-edge-btn').classList.add('mode-button-active');
                document.getElementById('current-mode-display').textContent = 'Add Edge';
                document.getElementById('graph-interaction-status').textContent = 'Click and drag from source to target node';
                canvas.style.cursor = 'pointer';
            } else if (mode === 'DELETE') {
                document.getElementById('mode-delete-btn').classList.add('mode-button-active');
                document.getElementById('current-mode-display').textContent = 'Delete';
                document.getElementById('graph-interaction-status').textContent = 'Click on a node or edge to delete it';
                canvas.style.cursor = 'not-allowed';
            }
            drawGraph();
        }

        canvas.addEventListener('mousedown', handleMouseDown);
        canvas.addEventListener('mousemove', handleMouseMove);
        canvas.addEventListener('mouseup', handleMouseUp);

        function handleMouseDown(event) {
            if (IS_RUNNING) return;
            const { x, y } = getCanvasCoordinates(event);
            
            if (currentMode === 'ADD_NODE') {
                const existingNode = getNodeAt(x, y);
                if (existingNode) {
                    document.getElementById('current-action').textContent = 'Node already exists here!';
                    return;
                }
                if (x < NODE_RADIUS || x > canvas.width - NODE_RADIUS || y < NODE_RADIUS || y > canvas.height - NODE_RADIUS) {
                    document.getElementById('current-action').textContent = 'Too close to canvas edge!';
                    return;
                }
                
                const newNodeName = String.fromCharCode(nextNodeId);
                GRAPH_DATA[newNodeName] = { x, y, neighbors: [] };
                NODE_NAMES.push(newNodeName);
                nextNodeId++;
                
                document.getElementById('current-action').textContent = `Node ${newNodeName} added at (${Math.round(x)}, ${Math.round(y)})`;
                populateDropdowns();
                updateGraphMetrics();
                analyzeGraphProperties();
                drawGraph();

            } else if (currentMode === 'ADD_EDGE') {
                const clickedNode = getNodeAt(x, y);
                if (clickedNode) {
                    startNodeForEdge = clickedNode;
                    isDrawingEdge = true;
                    currentEdgeX = x;
                    currentEdgeY = y;
                    document.getElementById('current-action').textContent = `Starting edge from ${startNodeForEdge}...`;
                } else {
                    document.getElementById('current-action').textContent = 'Click on a node to start!';
                }
            } else if (currentMode === 'DELETE') {
                const clickedNode = getNodeAt(x, y);
                if (clickedNode) {
                    deleteNode(clickedNode);
                    document.getElementById('current-action').textContent = `Node ${clickedNode} deleted!`;
                } else {
                    document.getElementById('current-action').textContent = 'Click on a node to delete it';
                }
            }
        }

        function handleMouseMove(event) {
            if (isDrawingEdge) {
                const { x, y } = getCanvasCoordinates(event);
                currentEdgeX = x;
                currentEdgeY = y;
                drawGraph();
            }
        }

        function handleMouseUp(event) {
            if (isDrawingEdge && currentMode === 'ADD_EDGE' && startNodeForEdge) {
                const { x, y } = getCanvasCoordinates(event);
                const endNode = getNodeAt(x, y);
                const isDirected = document.getElementById('directed-toggle').checked;

                if (endNode && endNode !== startNodeForEdge) {
                    const weight = parseFloat(document.getElementById('edge-weight').value);
                    if (isNaN(weight)) {
                        document.getElementById('current-action').textContent = 'Invalid weight!';
                    } else {
                        const startNeighbors = GRAPH_DATA[startNodeForEdge].neighbors;
                        let existingEdgeIndex = startNeighbors.findIndex(n => n.node === endNode);
                        
                        if (existingEdgeIndex === -1) {
                            startNeighbors.push({ node: endNode, weight: weight });
                            if (!isDirected) {
                                GRAPH_DATA[endNode].neighbors.push({ node: startNodeForEdge, weight: weight });
                            }
                            document.getElementById('current-action').textContent = `Edge ${startNodeForEdge}→${endNode} (w=${weight}) added`;
                        } else {
                            startNeighbors[existingEdgeIndex].weight = weight;
                            if (!isDirected) {
                                const endNeighbors = GRAPH_DATA[endNode].neighbors;
                                const reciprocalIndex = endNeighbors.findIndex(n => n.node === startNodeForEdge);
                                if (reciprocalIndex !== -1) {
                                    endNeighbors[reciprocalIndex].weight = weight;
                                }
                            }
                            document.getElementById('current-action').textContent = `Edge ${startNodeForEdge}→${endNode} weight updated to ${weight}`;
                        }
                        updateGraphMetrics();
                        analyzeGraphProperties();
                    }
                } else if (endNode === startNodeForEdge) {
                    document.getElementById('current-action').textContent = 'Cannot create self-loop!';
                } else {
                    document.getElementById('current-action').textContent = 'Edge cancelled';
                }

                isDrawingEdge = false;
                startNodeForEdge = null;
                drawGraph();
            }
        }

        function deleteNode(nodeKey) {
            delete GRAPH_DATA[nodeKey];
            NODE_NAMES = NODE_NAMES.filter(n => n !== nodeKey);
            
            for (const node of NODE_NAMES) {
                GRAPH_DATA[node].neighbors = GRAPH_DATA[node].neighbors.filter(n => n.node !== nodeKey);
            }
            
            populateDropdowns();
            updateGraphMetrics();
            analyzeGraphProperties();
            drawGraph();
        }

        // ==================== GRAPH UTILITIES ====================
        function updateGraphMetrics() {
            const V = NODE_NAMES.length;
            let E = 0;
            const isDirected = document.getElementById('directed-toggle').checked;
            
            for (const nodeKey of NODE_NAMES) {
                E += GRAPH_DATA[nodeKey].neighbors.length;
            }

            const maxEdges = isDirected ? V * (V - 1) : V * (V - 1) / 2;
            const currentEdges = isDirected ? E : E / 2;
            const density = V > 1 ? (currentEdges / maxEdges) * 100 : 0;
            
            document.getElementById('metric-V').textContent = V;
            document.getElementById('metric-E').textContent = currentEdges;
            document.getElementById('metric-density').textContent = `${density.toFixed(2)}%`;
        }

        function populateDropdowns() {
            const startSelect = document.getElementById('start-node');
            const targetSelect = document.getElementById('target-node');
            
            const currentStart = startSelect.value;
            const currentTarget = targetSelect.value;
            
            startSelect.innerHTML = '';
            targetSelect.innerHTML = '';

            if (NODE_NAMES.length === 0) {
                const placeholder = document.createElement('option');
                placeholder.value = '';
                placeholder.textContent = '(No nodes)';
                startSelect.appendChild(placeholder.cloneNode(true));
                targetSelect.appendChild(placeholder.cloneNode(true));
            }

            NODE_NAMES.forEach(name => {
                const option = document.createElement('option');
                option.value = name;
                option.textContent = name;
                startSelect.appendChild(option.cloneNode(true));
                targetSelect.appendChild(option);
            });
            
            if (NODE_NAMES.includes(currentStart)) {
                startSelect.value = currentStart;
            } else if (NODE_NAMES.length > 0) {
                startSelect.value = NODE_NAMES[0];
            }

            if (NODE_NAMES.includes(currentTarget)) {
                targetSelect.value = currentTarget;
            } else if (NODE_NAMES.length > 1) {
                targetSelect.value = NODE_NAMES[NODE_NAMES.length - 1];
            } else if (NODE_NAMES.length > 0) {
                targetSelect.value = NODE_NAMES[0];
            }
        }

        function updateComplexityDisplay() {
            const algo = document.getElementById('algorithm-select').value;
            const complexityElement = document.getElementById('time-complexity');
            
            const complexities = {
                'BFS': 'O(V + E)',
                'DFS': 'O(V + E)',
                'Dijkstra': 'O(E log V)',
                'BellmanFord': 'O(V * E)',
                'Prims': 'O(E log V)',
                'Kruskals': 'O(E log E)',
                'FloydWarshall': 'O(V³)'
            };
            
            complexityElement.textContent = complexities[algo] || 'O(V + E)';

            const isSP = (algo === 'Dijkstra' || algo === 'BellmanFord');
            const isMST = (algo === 'Prims' || algo === 'Kruskals');
            
            document.querySelector('label[for="start-node"]').textContent = isMST ? 'Start Node (Optional)' : 'Start Node';
            document.querySelector('label[for="target-node"]').textContent = isSP ? 'Target Node' : (isMST || algo === 'FloydWarshall' ? 'Not Used' : 'Target (Optional)');
        }

        function analyzeGraphProperties() {
            if (NODE_NAMES.length === 0) {
                document.getElementById('graph-properties').classList.add('hidden');
                return;
            }

            const properties = {
                connected: isConnected(),
                hasCycle: hasCycle(),
                hasNegativeWeight: hasNegativeWeights(),
                isBipartite: checkBipartite()
            };

            const propertiesList = document.getElementById('properties-list');
            propertiesList.innerHTML = `
                <p>✓ Connected: <span class="font-bold ${properties.connected ? 'text-green-600' : 'text-red-600'}">${properties.connected ? 'Yes' : 'No'}</span></p>
                <p>✓ Has Cycle: <span class="font-bold ${properties.hasCycle ? 'text-orange-600' : 'text-green-600'}">${properties.hasCycle ? 'Yes' : 'No'}</span></p>
                <p>✓ Negative Weights: <span class="font-bold ${properties.hasNegativeWeight ? 'text-red-600' : 'text-green-600'}">${properties.hasNegativeWeight ? 'Yes' : 'No'}</span></p>
                <p>✓ Bipartite: <span class="font-bold ${properties.isBipartite ? 'text-green-600' : 'text-gray-600'}">${properties.isBipartite ? 'Yes' : 'No'}</span></p>
            `;
            document.getElementById('graph-properties').classList.remove('hidden');
        }

        function isConnected() {
            if (NODE_NAMES.length === 0) return true;
            const visited = new Set();
            const queue = [NODE_NAMES[0]];
            
            while (queue.length > 0) {
                const current = queue.shift();
                if (visited.has(current)) continue;
                visited.add(current);
                
                for (const neighbor of GRAPH_DATA[current].neighbors) {
                    if (!visited.has(neighbor.node)) {
                        queue.push(neighbor.node);
                    }
                }
            }
            
            return visited.size === NODE_NAMES.length;
        }

        function hasCycle() {
            const visited = new Set();
            const recStack = new Set();
            
            function dfs(node, parent) {
                visited.add(node);
                recStack.add(node);
                
                for (const neighbor of GRAPH_DATA[node].neighbors) {
                    if (!visited.has(neighbor.node)) {
                        if (dfs(neighbor.node, node)) return true;
                    } else if (recStack.has(neighbor.node) && neighbor.node !== parent) {
                        return true;
                    }
                }
                
                recStack.delete(node);
                return false;
            }
            
            for (const node of NODE_NAMES) {
                if (!visited.has(node)) {
                    if (dfs(node, null)) return true;
                }
            }
            return false;
        }

        function hasNegativeWeights() {
            for (const nodeKey of NODE_NAMES) {
                if (GRAPH_DATA[nodeKey].neighbors.some(n => n.weight < 0)) {
                    return true;
                }
            }
            return false;
        }

        function checkBipartite() {
            if (NODE_NAMES.length === 0) return true;
            const color = {};
            
            for (const start of NODE_NAMES) {
                if (color[start] !== undefined) continue;
                
                const queue = [start];
                color[start] = 0;
                
                while (queue.length > 0) {
                    const current = queue.shift();
                    
                    for (const neighbor of GRAPH_DATA[current].neighbors) {
                        if (color[neighbor.node] === undefined) {
                            color[neighbor.node] = 1 - color[current];
                            queue.push(neighbor.node);
                        } else if (color[neighbor.node] === color[current]) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        // ==================== PRESET GRAPHS ====================
        function loadPresetGraph(type) {
            resetVisualization(true);
            const centerX = canvas.width / 2;
            const centerY = canvas.height / 2;
            const radius = Math.min(canvas.width, canvas.height) / 3;

            if (type === 'complete5') {
                for (let i = 0; i < 5; i++) {
                    const angle = (i * 2 * Math.PI / 5) - Math.PI / 2;
                    const nodeName = String.fromCharCode(65 + i);
                    GRAPH_DATA[nodeName] = {
                        x: centerX + radius * Math.cos(angle),
                        y: centerY + radius * Math.sin(angle),
                        neighbors: []
                    };
                    NODE_NAMES.push(nodeName);
                }
                for (let i = 0; i < 5; i++) {
                    for (let j = i + 1; j < 5; j++) {
                        const weight = Math.floor(Math.random() * 10) + 1;
                        GRAPH_DATA[NODE_NAMES[i]].neighbors.push({ node: NODE_NAMES[j], weight });
                        GRAPH_DATA[NODE_NAMES[j]].neighbors.push({ node: NODE_NAMES[i], weight });
                    }
                }
                nextNodeId = 70;
                document.getElementById('current-action').textContent = 'K5 Complete Graph loaded';

            } else if (type === 'bipartite') {
                for (let i = 0; i < 3; i++) {
                    const nodeName = String.fromCharCode(65 + i);
                    GRAPH_DATA[nodeName] = {
                        x: canvas.width * 0.25,
                        y: centerY + (i - 1) * 80,
                        neighbors: []
                    };
                    NODE_NAMES.push(nodeName);
                }
                for (let i = 0; i < 3; i++) {
                    const nodeName = String.fromCharCode(68 + i);
                    GRAPH_DATA[nodeName] = {
                        x: canvas.width * 0.75,
                        y: centerY + (i - 1) * 80,
                        neighbors: []
                    };
                    NODE_NAMES.push(nodeName);
                }
                for (let i = 0; i < 3; i++) {
                    for (let j = 3; j < 6; j++) {
                        const weight = Math.floor(Math.random() * 10) + 1;
                        GRAPH_DATA[NODE_NAMES[i]].neighbors.push({ node: NODE_NAMES[j], weight });
                        GRAPH_DATA[NODE_NAMES[j]].neighbors.push({ node: NODE_NAMES[i], weight });
                    }
                }
                nextNodeId = 71;
                document.getElementById('current-action').textContent = 'Bipartite Graph loaded';

            } else if (type === 'negative_cycle') {
                document.getElementById('directed-toggle').checked = true;
                for (let i = 0; i < 4; i++) {
                    const angle = (i * 2 * Math.PI / 4) - Math.PI / 2;
                    const nodeName = String.fromCharCode(65 + i);
                    GRAPH_DATA[nodeName] = {
                        x: centerX + radius * Math.cos(angle),
                        y: centerY + radius * Math.sin(angle),
                        neighbors: []
                    };
                    NODE_NAMES.push(nodeName);
                }
                GRAPH_DATA['A'].neighbors.push({ node: 'B', weight: 1 });
                GRAPH_DATA['B'].neighbors.push({ node: 'C', weight: -3 });
                GRAPH_DATA['C'].neighbors.push({ node: 'D', weight: 1 });
                GRAPH_DATA['D'].neighbors.push({ node: 'A', weight: 1 });
                nextNodeId = 69;
                document.getElementById('current-action').textContent = 'Negative Cycle Graph loaded (for Bellman-Ford testing)';

            } else if (type === 'sparse') {
                for (let i = 0; i < 6; i++) {
                    const nodeName = String.fromCharCode(65 + i);
                    GRAPH_DATA[nodeName] = {
                        x: centerX + (i % 3 - 1) * 150,
                        y: centerY + Math.floor(i / 3) * 120 - 60,
                        neighbors: []
                    };
                    NODE_NAMES.push(nodeName);
                }
                const edges = [['A','B',2], ['B','C',3], ['A','D',1], ['D','E',4], ['E','F',2]];
                edges.forEach(([u, v, w]) => {
                    GRAPH_DATA[u].neighbors.push({ node: v, weight: w });
                    GRAPH_DATA[v].neighbors.push({ node: u, weight: w });
                });
                nextNodeId = 71;
                document.getElementById('current-action').textContent = 'Sparse Tree Graph loaded';
            }

            populateDropdowns();
            updateGraphMetrics();
            analyzeGraphProperties();
            drawGraph();
        }

        function generateRandomGraph() {
            resetVisualization(true);
            const V = parseInt(document.getElementById('num-nodes-input').value) || 8;
            const E_target = parseInt(document.getElementById('num-edges-input').value) || 12;
            const isDirected = document.getElementById('directed-toggle').checked;
            const maxE = isDirected ? V * (V - 1) : V * (V - 1) / 2;

            if (V < 2 || V > 15) {
                document.getElementById('current-action').textContent = 'V must be between 2-15';
                return;
            }

            const E = Math.min(E_target, maxE);

            for (let i = 0; i < V; i++) {
                const nodeName = String.fromCharCode(65 + i);
                let x, y, overlap;
                let attempts = 0;
                do {
                    overlap = false;
                    x = Math.random() * (canvas.width - 4 * NODE_RADIUS) + 2 * NODE_RADIUS;
                    y = Math.random() * (canvas.height - 4 * NODE_RADIUS) + 2 * NODE_RADIUS;

                    for (const nodeKey in GRAPH_DATA) {
                        if (Math.hypot(GRAPH_DATA[nodeKey].x - x, GRAPH_DATA[nodeKey].y - y) < 4 * NODE_RADIUS) {
                            overlap = true;
                            break;
                        }
                    }
                    attempts++;
                } while (overlap && attempts < 50);

                GRAPH_DATA[nodeName] = { x, y, neighbors: [] };
                NODE_NAMES.push(nodeName);
            }
            nextNodeId = 65 + V;

            let edgesCount = 0;
            const existingEdges = new Set();
            
            while (edgesCount < E) {
                const u_index = Math.floor(Math.random() * V);
                let v_index = Math.floor(Math.random() * V);
                
                while (u_index === v_index) {
                    v_index = Math.floor(Math.random() * V);
                }

                const u = NODE_NAMES[u_index];
                const v = NODE_NAMES[v_index];
                const sortedEdge = u < v ? `${u}-${v}` : `${v}-${u}`;
                const directedEdge = `${u}->${v}`;

                if (isDirected && existingEdges.has(directedEdge)) continue;
                if (!isDirected && existingEdges.has(sortedEdge)) continue;
                
                const weight = Math.floor(Math.random() * 10) + 1;
                
                GRAPH_DATA[u].neighbors.push({ node: v, weight });
                if (isDirected) {
                    existingEdges.add(directedEdge);
                } else {
                    GRAPH_DATA[v].neighbors.push({ node: u, weight });
                    existingEdges.add(sortedEdge);
                }
                edgesCount++;
            }

            document.getElementById('current-action').textContent = `Random graph: V=${V}, E=${edgesCount}`;
            populateDropdowns();
            updateGraphMetrics();
            analyzeGraphProperties();
            drawGraph();
        }

        
        // ==================== ALGORITHMS ====================
        function runTraversal(startNode, isBFS) {
            const visited = new Set();           // Tracks which nodes are already visited
            const frontier = [startNode];        // Queue (BFS) or Stack (DFS) of nodes to process
            const history = [];                  // Steps recorded for visualization
            OPERATION_COUNT = 0;                 // For complexity display

            while (frontier.length > 0) {
                const current = isBFS ? frontier.shift() : frontier.pop();         // Remove from front or top
                OPERATION_COUNT++;
                
                if (visited.has(current)) continue;          // Skip if already processed
                visited.add(current);
                history.push({ 
                    type: 'visit', 
                    node: current, 
                    action: `${isBFS ? 'BFS' : 'DFS'}: Visiting ${current}`,
                    dataStructure: `${isBFS ? 'Queue' : 'Stack'}: [${frontier.join(', ')}]`
                });

                // Collect neighbors, sort alphabetically for stable visualization
                const neighbors = GRAPH_DATA[current].neighbors.map(n => n.node).sort();
                if (!isBFS) neighbors.reverse();

                for (const neighborKey of neighbors) {
                    if (!visited.has(neighborKey)) {
                        history.push({ 
                            type: 'explore', 
                            from: current, 
                            to: neighborKey, 
                            action: `Exploring edge ${current}→${neighborKey}`
                        });
                        if (!frontier.includes(neighborKey)) {       
                            frontier.push(neighborKey);              // Add neighbor for later visit
                        }
                    }
                }
            }

             showComplexity(isBFS ? "BFS" : "DFS");

            return { path: Array.from(visited).join(' → '), cost: null, history, operations: OPERATION_COUNT };
        }

        function runDijkstra(startNode, targetNode) {
            const distances = {};                         // shortest known distance to each node
            const previous = {};                            // previous node in shortest path
            const priorityQueue = new MinPriorityQueue();
            const history = [];
            OPERATION_COUNT = 0;

            for (const nodeKey of NODE_NAMES) { 
                distances[nodeKey] = Infinity; 
                previous[nodeKey] = null; 
            }
            distances[startNode] = 0;
            priorityQueue.enqueue({ node: startNode, distance: 0 });
            history.push({ type: 'init', action: `Initialize: ${startNode} dist=0` });

            while (priorityQueue.size() > 0) {
                const smallest = priorityQueue.dequeue();
                const current = smallest.node;
                OPERATION_COUNT++;

                if (smallest.distance > distances[current]) continue;         // skip outdated entries
                if (current === targetNode) break;                     // early stop when target reached

                history.push({ 
                    type: 'current', 
                    node: current, 
                    action: `Extract min: ${current} (dist=${distances[current].toFixed(2)})`,
                    dataStructure: `PQ size: ${priorityQueue.size()}`
                });

                for (const neighbor of GRAPH_DATA[current].neighbors) {
                    const nextNode = neighbor.node;
                    const weight = neighbor.weight;
                    const distance = distances[current] + weight;

                    if (distance < distances[nextNode]) {         // found shorter path
                        distances[nextNode] = distance;
                        previous[nextNode] = current;
                        history.push({ 
                            type: 'update', 
                            from: current,
                            to: nextNode,
                            node: nextNode, 
                            distance, 
                            action: `RELAX: ${nextNode} dist=${distance.toFixed(2)}`
                        });
                        priorityQueue.enqueue({ node: nextNode, distance });
                    }
                }
            }

            showComplexity("Dijkstra");

            if (distances[targetNode] !== Infinity) {
                const path = [];
                let curr = targetNode;
                while (curr) { path.unshift(curr); curr = previous[curr]; }
                return { path: path.join(' → '), cost: distances[targetNode], history, cycle: false, operations: OPERATION_COUNT };
            }
            return { path: null, cost: null, history, cycle: false, operations: OPERATION_COUNT };
        }

        function runBellmanFord(startNode, targetNode) {
            const distances = {};
            const previous = {};
            const history = [];
            const numNodes = NODE_NAMES.length;
            const allEdges = [];
            OPERATION_COUNT = 0;


            // Step 1: initialization & edge list
            for (const nodeKey of NODE_NAMES) { 
                distances[nodeKey] = Infinity; 
                previous[nodeKey] = null; 
                for (const neighbor of GRAPH_DATA[nodeKey].neighbors) {
                    allEdges.push({ u: nodeKey, v: neighbor.node, weight: neighbor.weight });
                }
            }
            distances[startNode] = 0;
            history.push({ type: 'init', action: `Bellman-Ford: ${numNodes - 1} passes` });
            
            // Step 2: relax edges |V|-1 times
            for (let i = 0; i < numNodes; i++) {
                let didRelax = false;
                
                if (i < numNodes - 1) {
                    history.push({ type: 'pass', action: `Pass ${i + 1}/${numNodes - 1}` });
                } else {
                    history.push({ type: 'cycle_check_start', action: `Cycle detection pass` });
                }

                for (const edge of allEdges) {
                    const { u, v, weight } = edge;
                    OPERATION_COUNT++;

                    if (distances[u] !== Infinity && distances[u] + weight < distances[v]) {
                        if (i === numNodes - 1) {

                             showComplexity("Bellman-Ford");

                            history.push({ type: 'negative_cycle', action: `NEGATIVE CYCLE at ${u}→${v}!` });
                            return { path: null, cost: null, history, cycle: true, operations: OPERATION_COUNT };
                        }
                        
                        distances[v] = distances[u] + weight;
                        previous[v] = u;
                        didRelax = true;
                        history.push({ type: 'relax', from: u, to: v, action: `RELAX: ${v} dist=${distances[v].toFixed(2)}` });
                    }
                }
                
                if (i < numNodes - 1 && !didRelax) {
                    history.push({ type: 'finish_early', action: `Early termination at pass ${i + 1}` });
                    break;
                }
            }

             showComplexity("Bellman-Ford");

            // Step 3: reconstruct path 
            if (distances[targetNode] !== Infinity) {
                const path = [];
                let curr = targetNode;
                while (curr) { path.unshift(curr); curr = previous[curr]; }
                return { path: path.join(' → '), cost: distances[targetNode], history, cycle: false, operations: OPERATION_COUNT };
            }
            return { path: null, cost: null, history, cycle: false, operations: OPERATION_COUNT };
        }

        function runPrims(startNode) {
            const isDirected = document.getElementById('directed-toggle').checked;
            if (isDirected) return { path: null, cost: null, error: 'MST requires Undirected', history: [] };
            
            const history = [];
            const mst = [];
            const minWeight = {};
            const previous = {};
            const priorityQueue = new MinPriorityQueue();
            let totalCost = 0;
            OPERATION_COUNT = 0;

            for (const nodeKey of NODE_NAMES) { 
                minWeight[nodeKey] = Infinity; 
                previous[nodeKey] = null; 
            }
            const start = startNode || NODE_NAMES[0];
            minWeight[start] = 0;
            priorityQueue.enqueue({ node: start, weight: 0 });
            history.push({ type: 'init', action: `Prim's: Start from ${start}` });

            while (priorityQueue.size() > 0 && mst.length < NODE_NAMES.length - 1) {
                const smallest = priorityQueue.dequeue();
                const u = smallest.node;
                OPERATION_COUNT++;

                if (previous[u] === 'VISITED') continue;
                
                const parent = previous[u];
                if (parent !== null) {
                    const edgeKey = u < parent ? `${u}-${parent}` : `${parent}-${u}`;
                    mst.push(edgeKey);
                    totalCost += minWeight[u];
                    history.push({ 
                        type: 'add_mst', 
                        from: u, 
                        to: parent, 
                        edgeKey, 
                        action: `Add edge ${parent}-${u} (w=${minWeight[u]}) | Cost: ${totalCost.toFixed(2)}`,
                        dataStructure: `MST edges: ${mst.length}`
                    });
                }
                previous[u] = 'VISITED';
                history.push({ type: 'current', node: u, action: `Process ${u}` });

                for (const neighbor of GRAPH_DATA[u].neighbors) {
                    const v = neighbor.node;
                    const weight = neighbor.weight;

                    if (previous[v] !== 'VISITED' && weight < minWeight[v]) {
                        minWeight[v] = weight;
                        previous[v] = u;
                        history.push({ 
                            type: 'update', 
                            from: u, 
                            to: v, 
                            weight, 
                            action: `Update: ${u}-${v} (w=${weight})` 
                        });
                        priorityQueue.enqueue({ node: v, weight });
                    }
                }
            }
            
            showComplexity("Prim");


            return { path: mst.join(', '), cost: totalCost, history, type: 'MST', operations: OPERATION_COUNT };
        }

        function runKruskals() {
            const isDirected = document.getElementById('directed-toggle').checked;
            if (isDirected) return { path: null, cost: null, error: 'MST requires Undirected', history: [] };

            const history = [];
            const allEdges = [];
            const mst = [];
            let totalCost = 0;
            OPERATION_COUNT = 0;

            for (const u of NODE_NAMES) {
                for (const neighbor of GRAPH_DATA[u].neighbors) {
                    const v = neighbor.node;
                    if (u < v) {
                        allEdges.push({ u, v, weight: neighbor.weight });
                    }
                }
            }

            allEdges.sort((a, b) => a.weight - b.weight);
            history.push({ type: 'init', action: `Kruskal's: Sorted ${allEdges.length} edges` });

            const ds = new DisjointSet(NODE_NAMES);

            for (const edge of allEdges) {
                const { u, v, weight } = edge;
                OPERATION_COUNT++;

                if (ds.union(u, v)) {
                    const edgeKey = `${u}-${v}`;
                    mst.push(edgeKey);
                    totalCost += weight;
                    history.push({ 
                        type: 'add_mst', 
                        from: u, 
                        to: v, 
                        edgeKey, 
                        action: `Add ${u}-${v} (w=${weight}) | Cost: ${totalCost.toFixed(2)}`,
                        dataStructure: `MST edges: ${mst.length}`
                    });
                } else {
                    history.push({ 
                        type: 'skip', 
                        from: u, 
                        to: v, 
                        action: `Skip ${u}-${v}: Forms cycle` 
                    });
                }
            }

            showComplexity("Kruskal");

            return { path: mst.join(', '), cost: totalCost, history, type: 'MST', operations: OPERATION_COUNT };
        }
        
        function runFloydWarshall() {
            const history = [];
            const V = NODE_NAMES.length;
            const nodeIndex = {};
            NODE_NAMES.forEach((node, i) => nodeIndex[node] = i);
            const dist = Array.from({ length: V }, () => Array(V).fill(Infinity));
            const next = Array.from({ length: V }, () => Array(V).fill(null));
            OPERATION_COUNT = 0;

            for (let i = 0; i < V; i++) {
                dist[i][i] = 0;
                for (const neighbor of GRAPH_DATA[NODE_NAMES[i]].neighbors) {
                    const j = nodeIndex[neighbor.node];
                    dist[i][j] = neighbor.weight;
                    next[i][j] = neighbor.node;
                }
            }
            history.push({ type: 'init', action: `Floyd-Warshall: Init matrix` });

            for (let k = 0; k < V; k++) {
                const k_node = NODE_NAMES[k];
                history.push({ type: 'pass', node: k_node, action: `Intermediate: k=${k_node}` });

                for (let i = 0; i < V; i++) {
                    const i_node = NODE_NAMES[i];
                    for (let j = 0; j < V; j++) {
                        const j_node = NODE_NAMES[j];
                        OPERATION_COUNT++;

                        if (dist[i][k] !== Infinity && dist[k][j] !== Infinity && dist[i][k] + dist[k][j] < dist[i][j]) {
                            dist[i][j] = dist[i][k] + dist[k][j];
                            next[i][j] = next[i][k];
                            history.push({ 
                                type: 'update', 
                                from: i_node, 
                                to: j_node, 
                                node: k_node, 
                                action: `Update: ${i_node}→${j_node} via ${k_node} = ${dist[i][j].toFixed(2)}` 
                            });
                        }
                    }
                }
            }

            for (let i = 0; i < V; i++) {
                if (dist[i][i] < 0) {
                    history.push({ type: 'negative_cycle', action: `NEGATIVE CYCLE!` });
                    showComplexity("Floyd-Warshall");
                    return { path: null, cost: null, history, cycle: true, distMatrix: dist, nextMatrix: next, operations: OPERATION_COUNT };
                }
            }
            showComplexity("Floyd-Warshall");

            return { path: 'All-Pairs SP Computed', cost: null, history, cycle: false, distMatrix: dist, nextMatrix: next, operations: OPERATION_COUNT };
        }

        // ==================== PSEUDOCODE ====================
        const PSEUDOCODE = {
            BFS: `1. Initialize queue Q with start node
2. Mark start as visited
3. While Q is not empty:
4.   u = dequeue from Q
5.   Process node u
6.   For each neighbor v of u:
7.     If v not visited:
8.       Mark v as visited
9.       Enqueue v to Q`,
            DFS: `1. Initialize stack S with start node
2. Mark start as visited
3. While S is not empty:
4.   u = pop from S
5.   Process node u
6.   For each neighbor v of u:
7.     If v not visited:
8.       Mark v as visited
9.       Push v to S`,
            Dijkstra: `1. Initialize distances[v] = ∞ for all v
2. distances[start] = 0
3. Add start to priority queue PQ
4. While PQ is not empty:
5.   u = extract min from PQ
6.   For each neighbor v of u:
7.     newDist = distances[u] + weight(u,v)
8.     If newDist < distances[v]:
9.       distances[v] = newDist
10.      Add v to PQ with priority newDist`,
            BellmanFord: `1. Initialize distances[v] = ∞ for all v
2. distances[start] = 0
3. For i = 1 to |V|-1:
4.   For each edge (u,v) with weight w:
5.     If distances[u] + w < distances[v]:
6.       distances[v] = distances[u] + w
7. For each edge (u,v) with weight w:
8.   If distances[u] + w < distances[v]:
9.     Report negative cycle`,
            Prims: `1. Initialize minWeight[v] = ∞ for all v
2. minWeight[start] = 0
3. Add start to priority queue PQ
4. While PQ not empty and MST incomplete:
5.   u = extract min from PQ
6.   Add edge to MST
7.   For each neighbor v of u:
8.     If v not in MST and weight(u,v) < minWeight[v]:
9.       minWeight[v] = weight(u,v)
10.      Add v to PQ`,
            Kruskals: `1. Sort all edges by weight
2. Initialize disjoint set DS for all nodes
3. Initialize MST as empty
4. For each edge (u,v) in sorted order:
5.   If find(u) ≠ find(v):
6.     Add edge (u,v) to MST
7.     Union(u, v)
8. Return MST`,
            FloydWarshall: `1. Initialize dist[i][j] = ∞ for all i,j
2. For each edge (i,j): dist[i][j] = weight(i,j)
3. For each i: dist[i][i] = 0
4. For k = 1 to |V|:
5.   For i = 1 to |V|:
6.     For j = 1 to |V|:
7.       If dist[i][k] + dist[k][j] < dist[i][j]:
8.         dist[i][j] = dist[i][k] + dist[k][j]
9. Check diagonal for negative cycles`
        };

        function showPseudocode(algo) {
            const panel = document.getElementById('pseudocode-panel');
            const content = document.getElementById('pseudocode-content');
            content.textContent = PSEUDOCODE[algo] || '';
            panel.classList.remove('hidden');
        }

        function updatePseudocodeHighlight(stepType) {
            // This would highlight the current line - simplified for now
        }

        // ==================== DATA STRUCTURE VISUALIZATION ====================
        function updateDataStructureView(step) {
            if (!step || !step.dataStructure) {
                document.getElementById('ds-panel').classList.add('hidden');
                return;
            }

            const panel = document.getElementById('ds-panel');
            const content = document.getElementById('ds-content');
            
            content.innerHTML = `
                <div class="data-structure-box">
                    <p class="text-xs font-bold mb-1">Current State:</p>
                    <p class="text-sm">${step.dataStructure}</p>
                </div>
            `;
            
            panel.classList.remove('hidden');
        }

        // ==================== VISUALIZATION CONTROL ====================
        function startVisualization() {
            if (IS_RUNNING) return;
            if (NODE_NAMES.length === 0) {
                document.getElementById('current-action').textContent = 'Graph is empty!';
                return;
            }

            resetVisualization(false);
            document.getElementById('comparison-results').classList.add('hidden');

            const algo = document.getElementById('algorithm-select').value;
            const start = document.getElementById('start-node').value;
            const target = document.getElementById('target-node').value;
            const isDirected = document.getElementById('directed-toggle').checked;
            
            if (!start || !GRAPH_DATA[start]) {
                document.getElementById('current-action').textContent = 'Select valid Start Node';
                return;
            }
            if ((algo === 'Dijkstra' || algo === 'BellmanFord') && (!target || !GRAPH_DATA[target])) {
                document.getElementById('current-action').textContent = 'Select valid Target Node';
                return;
            }
            if ((algo === 'Prims' || algo === 'Kruskals') && isDirected) {
                document.getElementById('current-action').textContent = 'MST requires Undirected graph!';
                return;
            }
            if (algo === 'Dijkstra' && hasNegativeWeights()) {
                document.getElementById('current-action').textContent = 'Dijkstra requires non-negative weights!';
                return;
            }
            
            let result;
            try {
                START_TIME = performance.now();
                if (algo === 'BFS') result = runTraversal(start, true);
                else if (algo === 'DFS') result = runTraversal(start, false);
                else if (algo === 'Dijkstra') result = runDijkstra(start, target);
                else if (algo === 'BellmanFord') result = runBellmanFord(start, target);
                else if (algo === 'Prims') result = runPrims(start);
                else if (algo === 'Kruskals') result = runKruskals();
                else if (algo === 'FloydWarshall') result = runFloydWarshall();
                END_TIME = performance.now();
            } catch (error) {
                console.error("Algorithm error:", error);
                document.getElementById('current-action').textContent = 'Error during execution';
                return;
            }

            ALGORITHM_HISTORY = result.history;
            FINAL_PATH = result;

            IS_RUNNING = true;
            document.getElementById('start-btn').disabled = true;
            document.getElementById('next-btn').disabled = false;
            document.getElementById('auto-btn').disabled = false;
            document.getElementById('time-taken').textContent = `${(END_TIME - START_TIME).toFixed(2)} ms`;
            document.getElementById('total-steps').textContent = ALGORITHM_HISTORY.length;
            document.getElementById('op-counter').textContent = result.operations || 0;
            
            showPseudocode(algo);
            drawStep();
        }

        function nextStep() {
            if (!IS_RUNNING) return;

            if (CURRENT_STEP >= ALGORITHM_HISTORY.length) {
                drawFinalResult();
                return;
            }

            CURRENT_STEP++;
            drawStep();
            
            if (CURRENT_STEP >= ALGORITHM_HISTORY.length) {
                document.getElementById('next-btn').disabled = true;
                document.getElementById('auto-btn').disabled = true;
                document.getElementById('current-action').textContent = 'Algorithm complete!';
                drawFinalResult();
            }
        }

        function toggleAutoPlay() {
            AUTO_PLAY = !AUTO_PLAY;
            const btn = document.getElementById('auto-btn');
            
            if (AUTO_PLAY) {
                btn.textContent = 'Pause';
                btn.classList.remove('bg-purple-500', 'hover:bg-purple-600');
                btn.classList.add('bg-yellow-500', 'hover:bg-yellow-600');
                document.getElementById('next-btn').disabled = true;
                
                const speed = parseInt(document.getElementById('speed-slider').value);
                AUTO_PLAY_INTERVAL = setInterval(() => {
                    if (CURRENT_STEP >= ALGORITHM_HISTORY.length) {
                        toggleAutoPlay();
                        return;
                    }
                    nextStep();
                }, speed);
            } else {
                btn.textContent = 'Auto Play';
                btn.classList.remove('bg-yellow-500', 'hover:bg-yellow-600');
                btn.classList.add('bg-purple-500', 'hover:bg-purple-600');
                document.getElementById('next-btn').disabled = false;
                clearInterval(AUTO_PLAY_INTERVAL);
            }
        }

        function drawStep() {
            const step = ALGORITHM_HISTORY[CURRENT_STEP - 1];
            if (!step) return;

            const visitedNodes = new Set();
            const highlightedEdges = new Set();
            const finalPathSet = new Set();
            const isDirected = document.getElementById('directed-toggle').checked;
            const algo = document.getElementById('algorithm-select').value;
            let mstCost = null;

            for (let i = 0; i < CURRENT_STEP; i++) {
                const historyStep = ALGORITHM_HISTORY[i];
                
                if (historyStep.node) {
                    visitedNodes.add(historyStep.node);
                }
                
                if (historyStep.type === 'add_mst') {
                    const edgeKey = historyStep.edgeKey;
                    finalPathSet.add(edgeKey);
                    edgeKey.split('-').forEach(node => finalPathSet.add(node));
                } else if (historyStep.from && historyStep.to) {
                    const u = historyStep.from;
                    const v = historyStep.to;
                    const edgeKey = isDirected ? `${u}-${v}` : (u < v ? `${u}-${v}` : `${v}-${u}`);
                    highlightedEdges.add(edgeKey);
                }
                
                if (historyStep.action && historyStep.action.includes('Cost:')) {
                    const match = historyStep.action.match(/Cost: ([\d.]+)/);
                    if (match) mstCost = parseFloat(match[1]);
                }
            }
            
            document.getElementById('step-counter').textContent = CURRENT_STEP;
            document.getElementById('current-action').textContent = step.action;
            updateDataStructureView(step);
            
            if (algo === 'Prims' || algo === 'Kruskals') {
                drawGraph(visitedNodes, highlightedEdges, finalPathSet, mstCost);
            } else {
                drawGraph(visitedNodes, highlightedEdges, new Set());
            }
        }

        function drawFinalResult() {
            const algo = document.getElementById('algorithm-select').value;
            const start = document.getElementById('start-node').value;
            const target = document.getElementById('target-node').value;
            
            let resultText = '';
            let finalPathSet = new Set();

            if (FINAL_PATH.cycle) {
                resultText = `<span class="text-red-600 font-bold">NEGATIVE CYCLE DETECTED!</span>`;
                drawGraph();
            } else if (algo === 'FloydWarshall') {
                resultText = `All-Pairs Shortest Paths computed. Matrix logged to console (F12).`;
                console.log("=== FLOYD-WARSHALL RESULTS ===");
                console.table(FINAL_PATH.distMatrix);
                drawGraph();
            } else if (algo === 'BFS' || algo === 'DFS') {
                resultText = `Traversal: ${FINAL_PATH.path}`;
                FINAL_PATH.path.split(' → ').forEach(node => finalPathSet.add(node));
                drawGraph(finalPathSet, new Set(), finalPathSet);
            } else if (algo === 'Dijkstra' || algo === 'BellmanFord') {
                if (FINAL_PATH.path) {
                    resultText = `Path ${start}→${target}: ${FINAL_PATH.path} (Cost: ${FINAL_PATH.cost.toFixed(2)})`;
                    FINAL_PATH.path.split(' → ').forEach(node => finalPathSet.add(node));
                    const pathNodes = FINAL_PATH.path.split(' → ');
                    for (let i = 0; i < pathNodes.length - 1; i++) {
                        const u = pathNodes[i];
                        const v = pathNodes[i + 1];
                        finalPathSet.add(`${u}-${v}`);
                    }
                    drawGraph(new Set(), new Set(), finalPathSet);
                } else {
                    resultText = `No path from ${start} to ${target}`;
                    drawGraph();
                }
            } else if (algo === 'Prims' || algo === 'Kruskals') {
                if (FINAL_PATH.path) {
                    resultText = `MST: ${FINAL_PATH.path} | Cost: ${FINAL_PATH.cost.toFixed(2)}`;
                    FINAL_PATH.path.split(', ').forEach(edgeKey => {
                        finalPathSet.add(edgeKey);
                        edgeKey.split('-').forEach(node => finalPathSet.add(node));
                    });
                    drawGraph(new Set(), new Set(), finalPathSet, FINAL_PATH.cost);
                } else {
                    resultText = `MST failed (disconnected graph)`;
                    drawGraph();
                }
            }

            document.getElementById('final-result').innerHTML = resultText;
        }

        function resetVisualization(fullReset = false) {
            ALGORITHM_HISTORY = [];
            CURRENT_STEP = 0;
            IS_RUNNING = false;
            START_TIME = 0;
            END_TIME = 0;
            FINAL_PATH = null;
            OPERATION_COUNT = 0;
            
            if (AUTO_PLAY) toggleAutoPlay();
            
            document.getElementById('start-btn').disabled = false;
            document.getElementById('next-btn').disabled = true;
            document.getElementById('auto-btn').disabled = true;
            document.getElementById('step-counter').textContent = '0';
            document.getElementById('total-steps').textContent = '0';
            document.getElementById('time-taken').textContent = 'N/A';
            document.getElementById('op-counter').textContent = '0';
            document.getElementById('final-result').textContent = '—';
            document.getElementById('current-action').textContent = fullReset ? 'Graph cleared' : 'Ready to start';
            document.getElementById('comparison-results').classList.add('hidden');
            document.getElementById('pseudocode-panel').classList.add('hidden');
            document.getElementById('ds-panel').classList.add('hidden');
            
            if (fullReset) {
                GRAPH_DATA = {};
                NODE_NAMES = [];
                nextNodeId = 65;
                populateDropdowns();
                document.getElementById('graph-properties').classList.add('hidden');
            }

            updateGraphMetrics();
            drawGraph();
        }

        // ==================== COMPARISON ====================
        function runAllAlgorithms() {
            if (IS_RUNNING) return;
            if (NODE_NAMES.length === 0) {
                document.getElementById('current-action').textContent = 'Graph is empty!';
                return;
            }

            resetVisualization(false);
            
            const start = document.getElementById('start-node').value;
            const target = document.getElementById('target-node').value;
            const isDirected = document.getElementById('directed-toggle').checked;

            if (!start || !GRAPH_DATA[start]) {
                document.getElementById('current-action').textContent = 'Select valid Start Node';
                return;
            }

            const hasNegWeight = hasNegativeWeights();
            
            const algorithms = [
                { id: 'BFS', name: 'BFS' },
                { id: 'DFS', name: 'DFS' },
                { id: 'Dijkstra', name: 'Dijkstra' },
                { id: 'BellmanFord', name: 'Bellman-Ford' },
                { id: 'Prims', name: "Prim's" },
                { id: 'Kruskals', name: "Kruskal's" },
                { id: 'FloydWarshall', name: 'Floyd-Warshall' },
            ];

            const comparisonResults = [];

            algorithms.forEach(algoInfo => {
                const algoId = algoInfo.id;
                let result = { time: 0, path: 'N/A', cost: 'N/A', cycle: false, error: false, operations: 0 };

                if (algoId === 'Dijkstra' && hasNegWeight) {
                    result.error = true;
                    result.path = 'Skipped: Neg. Weight';
                    result.time = Infinity;
                } else if ((algoId === 'Prims' || algoId === 'Kruskals') && isDirected) {
                    result.error = true;
                    result.path = 'Skipped: Directed';
                    result.time = Infinity;
                } else {
                    const startTime = performance.now();
                    
                    if (algoId === 'BFS') result = runTraversal(start, true);
                    else if (algoId === 'DFS') result = runTraversal(start, false);
                    else if (algoId === 'Dijkstra') result = runDijkstra(start, target);
                    else if (algoId === 'BellmanFord') result = runBellmanFord(start, target);
                    else if (algoId === 'Prims') result = runPrims(start);
                    else if (algoId === 'Kruskals') result = runKruskals();
                    else if (algoId === 'FloydWarshall') result = runFloydWarshall();
                    
                    result.time = performance.now() - startTime;
                }

                comparisonResults.push({
                    name: algoInfo.name,
                    time: result.time,
                    cost: result.cost,
                    path: result.path,
                    cycle: result.cycle,
                    error: result.error,
                    operations: result.operations || 0
                });
            });

            document.getElementById('current-action').textContent = 'Comparison complete!';
            displayComparisonResults(comparisonResults);
        }

        // ==================== INITIALIZATION ====================
        document.getElementById('speed-slider').addEventListener('input', function() {
            document.getElementById('speed-display').textContent = this.value;
        });

        window.onload = function() {
            initializeCanvas();
            populateDropdowns();
            setMode('ADD_NODE');
            updateComplexityDisplay();
            window.addEventListener('resize', initializeCanvas);
        };

        // ======================
// TIME COMPLEXITY GRAPH
// ======================

// Create Chart Context
// ======================
// SINGLE-CURVE TIME COMPLEXITY GRAPH
// ======================
const ctxChart = document.getElementById('complexityChart').getContext('2d');
const n = Array.from({ length: 30 }, (_, i) => i + 1);

// Predefined growth formulas
const complexityData = {
  'O(1)':      n.map(() => 1),
  'O(log n)':  n.map(x => Math.log2(x)),
  'O(n)':      n.map(x => x),
  'O(n log n)':n.map(x => x * Math.log2(x)),
  'O(n²)':     n.map(x => x * x),
  'O(n³)':     n.map(x => x ** 3),
};

// Initial empty chart
const complexityChart = new Chart(ctxChart, {
  type: 'line',
  data: {
    labels: n,
    datasets: [],
  },
  options: {
    animation: { duration: 1200 },
    plugins: {
      legend: { display: false },
      title: { display: true, text: '', color: 'white' }
    },
    scales: {
      x: { ticks: { color: 'white' }, grid: { color: '#333' } },
      y: { ticks: { color: 'white' }, grid: { color: '#333' } }
    }
  }
});

// Map each algorithm → its Big-O
const algoComplexityMap = {
  'BFS': 'O(n)',
  'DFS': 'O(n)',
  'Dijkstra': 'O(n log n)',
  'Prim': 'O(n log n)',
  'Kruskal': 'O(n log n)',
  'Bellman-Ford': 'O(n²)',
  'Floyd-Warshall': 'O(n³)',
  'Default': 'O(1)'
};

// When algorithm finishes running
function showComplexity(algoName) {
  const label = algoComplexityMap[algoName] || algoComplexityMap['Default'];
  const color = '#a855f7'; // violet line (like your image)

  // Update title
  complexityChart.options.plugins.title.text = label;
  document.getElementById('complexity-title').innerText = `Time Complexity: ${label}`;

  // Update dataset — only one visible curve
  complexityChart.data.datasets = [
    {
      label,
      data: complexityData[label],
      borderColor: color,
      borderWidth: 3,
      tension: 0.2,
      fill: false
    }
  ];

  complexityChart.update();
}
