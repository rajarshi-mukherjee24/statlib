import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
  {{<link rel="stylesheet" href="static/style.css"/>}},
  {{<script src="static/scripts.js"></script>}},
]

def config : RenderConfig := {
  extraHead := extraHead,
  sourceLink := some "https://github.com/stat-lib/stat-lib.github.io",
  issueLink := some "https://github.com/stat-lib/stat-lib.github.io/issues",
}

def main := manualMain (%doc Manual.Front) (config := config)
