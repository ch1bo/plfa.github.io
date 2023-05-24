{-# OPTIONS --guardedness #-}
module hello where

open import IO

main : Main
main = run (putStrLn "Hello agda!")
