failed=0
for i in {1..1000}
do
    python3 treegen.py > a.tr
    if dune exec ./main.exe 0 < a.tr
    then 
        if ((i % 100 == 0))
        then 
            echo ${i}
        fi
    else
        echo ${i} $?
        failed=1
        break
    fi
done

if (( failed == 0 ))
then
    rm a.tr
fi
