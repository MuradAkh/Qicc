// Thanks to
// https://stackoverflow.com/questions/48563969/c-like-mutex-in-nodejs

interface PromiseResult {
    resolve(value?: unknown): void
    reject(reason?: any): void
}

export default class Mutex {

    queue: PromiseResult[]
    locked: boolean

    constructor () {
        this.queue = [];
        this.locked = false;
    }

    lock = () : Promise<void> => {
        return new Promise((resolve, reject) => {
            if (this.locked) {
                this.queue.push({resolve, reject} as PromiseResult);
            } else {
                this.locked = true;
                resolve();
            }
        });
    }

    release = () : void => {
        if (this.queue.length > 0) {
            const {resolve} = this.queue.shift()!;
            resolve();
        } else {
            this.locked = false;
        }
    }
}

