/*
 * Copyright 2016 WebAssembly Community Group participants
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//
// wasm-dwarf-dump console tool
//

#include "support/colors.h"
#include "support/command-line.h"
#include "support/file.h"
#include "wasm-io.h"
#include "wasm-printing.h"
#include "wasm-debug.h"

using namespace cashew;
using namespace wasm;

int main(int argc, const char* argv[]) {
  std::string sourceMapFilename;
  Options options("wasm-dwarf-dump",
                  "Dump DWARF debug info of a .wasm file");
  options
    .add_positional("INFILE",
                    Options::Arguments::One,
                    [](Options* o, const std::string& argument) {
                      o->extra["infile"] = argument;
                    });
  options.parse(argc, argv);

  Module wasm;
  try {
    ModuleReader().readBinary(options.extra["infile"], wasm, sourceMapFilename);
  } catch (ParseException& p) {
    p.dump(std::cerr);
    std::cerr << '\n';
    Fatal() << "error in parsing wasm binary";
  } catch (MapParseException& p) {
    p.dump(std::cerr);
    std::cerr << '\n';
    Fatal() << "error in parsing wasm source mapping";
  }

  wasm::Debug::dumpDWARF(wasm);
}
