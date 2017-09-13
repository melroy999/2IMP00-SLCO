# Race Condition Explorer tool, v0.1, 2017
#
# Update History:
#

# Start of program

from help_on_error_argument_parser import HelpOnErrorArgumentParser
import argparse
import logging
import logging.config
import sys
import os
import aut

def main():
	# setup logging
	file_handler    = logging.FileHandler(filename='rc_explorer.log', mode='w')
	console_handler = logging.StreamHandler(stream=sys.stdout)
	file_handler.setLevel(logging.INFO)
	console_handler.setLevel(logging.DEBUG)
	logging.basicConfig(format='%(asctime)s - %(levelname)s: %(message)s',
						datefmt='%Y-%m-%d %H:%M:%S',
						level=logging.DEBUG,
						handlers=[file_handler, console_handler])
	
	# parse arguments
	parser = HelpOnErrorArgumentParser(
		description='Race Condition Explorer: finds race conditions in state spaces in aut format, where labels are formatted as RW_Object(Read set, Write set)',
		formatter_class=argparse.ArgumentDefaultsHelpFormatter
	)
	parser.add_argument("INPUT_LTS", type=str, help="LTS file in aut format")
	parser.add_argument("-o", "--out", type=str, default="INPUT_LTS.rc", help="Output file name")
	parser.add_argument("-q", "--quiet", action='store_true', help="Quiet mode, print no messages to screen")
	
	args = vars(parser.parse_args())
	
	# set options
	if args['quiet']:
		console_handler.setLevel(logging.CRITICAL + 1)
	
	lts_path = args['INPUT_LTS']
	if not lts_path.endswith('.aut'):
		lts_path = lts_path + ".aut"
	
	out_path = args['out']
	if out_path == 'INPUT_LTS.rc':
		out_path = lts_path[:-4] + '.rc'
	
	logging.info('Starting Race Condition Explorer')
	logging.info('Input LTS  : %s', lts_path)
	logging.info('Output File: %s', out_path)
	
	lts_dir, lts_name = os.path.split(lts_path)
	header, trans, acts = aut.read(lts_dir, lts_name)
	
	print(header)
	print(trans)
	print(acts)
	
	logging.info('Finished, output written to %s', out_path)
	logging.shutdown()


if __name__ == '__main__':
	main()
