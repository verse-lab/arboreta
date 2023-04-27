failed=0
for i in {1..100}
do
    echo "Test" ${i}

    python3 treegen.py > a.tr
    if dune exec ./main.exe testjoin 0 b.tr < a.tr
    then 
        echo "Join test OK. "
    else
        echo "Failed on test" ${i} "with error code" $?
        failed=1
        break
    fi
    
    if python3 mutualrespect_checker.py a.tr b.tr 30 c.tr
    then 
        echo "Mutual respect test OK. "
    else
        echo "Failed on test" ${i} "with error code" $?
        failed=2
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
