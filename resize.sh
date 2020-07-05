#! /bin/bash

for f in $(ls unitals/*.png)
do
    width=$(identify -format "%w" $f)
    height=$(identify -format "%h" $f)
    if [ "$width" == "" ] || [ "$height" == "" ] || [ "$width" -gt 3840 ] || [ "$height" -gt 2160 ]
    then
        echo "$f"
        convert $f -resize 3840x2160 $f
    fi
done
