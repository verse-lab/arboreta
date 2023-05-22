failed=0
for i in {1..1000}
do
    python3 respect_treegen.py > a.tr
    if dune exec ./main.exe testjoin 0 b.tr < a.tr
    then 
        if ((i % 100 == 0))
        then 
            echo "Passed" ${i} "tests."
        fi
    else
        echo "Failed on test #" ${i} "with error code" $?
        failed=1
        break
    fi
    
    if [ -f "b.tr" ];
    then
        rm b.tr
    fi
done

if ((failed == 0))
then
    rm a.tr
fi
