#!/usr/bin/env python

import os;

# Build a new version of the jSMTLIB jar for testing
print('############ Start building ############')
os.system('./buildRelease');

# Run the functional tests in the tests directory
# For each input file, output an intermediate output in peticodiac format
# Compare the output with expected output pre-determined
print('\n\n############ Running Functional Tests ############')
cwd = os.getcwd()
tests_dir = os.path.join(cwd, 'tests')
number_of_tests = 0
number_of_failed_tests = 0
failed_tests = []

for path, dirs, files in os.walk(tests_dir):
    files.sort()
    for test_file in files:
        if (test_file.endswith('smt2')):
            number_of_tests += 1
            full_test_file_path = os.path.join(path, test_file)
            print('\n#### Running test {}'.format(test_file))
            java_command = 'java -jar jSMTLIB.jar {} --solver peticodiac --exec /Users/tony/dev/yices-1.0.40/bin/yices --peticodiacout ./tests'.format(full_test_file_path)
            os.system(java_command)

            actual_output_file = '{}.peticodiac'.format(test_file)
            actual_output_file_path = os.path.join(path, actual_output_file)
            expected_output_file = '{}.peticodiac.{}'.format(test_file, 'expected')
            expected_output_file_path = os.path.join(path, expected_output_file)
            test_result = os.system('diff {} {}'.format(actual_output_file_path, expected_output_file_path))
            if (test_result == 0):
                print('# Test {} completed successfully'.format(test_file))
            else:
                print('# Test {} failed'.format(test_file))
                number_of_failed_tests += 1
                failed_tests.append(test_file)

print('\n\n############ Test Result ############')
print('Total {} tests. {} tests failed'.format(number_of_tests, number_of_failed_tests))
if (failed_tests):
    print('\nThe following test failed:')
    for failed_test in failed_tests:
        print('\t{}'.format(failed_test))
