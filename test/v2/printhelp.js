const fs = require('fs');

const lines = fs.readFileSync(process.argv[2], 'utf-8').split('\n');
lines.map(line => line.split(": ")[1]).forEach(l => console.log(l)) 