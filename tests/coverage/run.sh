#!/bin/bash -e

pattern="${1:?requires regex pattern as first argument}"

input="
:set +dis:invariant_check
:coverage A64 $pattern
"

output="$(echo "$input" | asli)"

# substitute paths of the form <data:[...]> with ./[...]
echo "$output" | sed 's#<data:\([^>]*\)>#./\1#g'
