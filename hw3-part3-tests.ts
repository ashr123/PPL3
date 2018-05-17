import * as assert from "assert";
import {evalParse4} from './L4-eval-box';
import {evalParse} from "./L3-eval";

// assert.deepEqual(evalParse4(`
// (L4 (define loop (lambda (x) (loop x)))
//     ((lambda ((f lazy)) 1) (loop 0)))`),
// 	1);
// assert.deepEqual(evalParse4(`
//     (L4 (if ((lambda ((x lazy)) (= x 10)) 10) #t #f))`),
// 	true);

// assert.deepEqual(evalParse(`
//     (L3 (if ((lambda ((x lazy)) (= x 10)) 10) #t #f))`),
// 	true);

assert.deepEqual(evalParse(`
    (L3 (if ((lambda (x) (= x 10)) 10) #t #f))`),
	true);