echo "Building language implementation..."

echo "Building interpreter..."
cd ./duckpond
dune build
cd ..

if [ -e duckpond.exe ] 
then rm -f ./duckpond.exe
fi
mv -f ./duckpond/_build/default/src/duckpond.exe ./duckpond.exe

echo "Done"
