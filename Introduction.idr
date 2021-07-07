module Introduction

-- This is a simple comment

-- Import statements
import Data.Vect
import public Syntax.PreorderReasoning


-- All the functions/definitions in this module must be total.
-- Total definitions can be safely used in proofs and type level programming
-- %default total

data Day
  = Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday

data Workday : Day -> Type where
  MondayW : Workday Monday
  TuesdayW : Workday Tuesday
  WednesdayW : Workday Wednesday
  ThursdayW : Workday Thursday
  FridayW : Workday Friday

-- test : Workday Monday
-- test = MondayW

-- test2 : Workday Tuesday
-- test2 = TuesdayW

total
printWorkday : (d : Day) -> {auto _ : Workday d} -> String
printWorkday Monday = ?printWorkday_rhs_1
printWorkday Tuesday = ?printWorkday_rhs_2
printWorkday Wednesday = ?printWorkday_rhs_3
printWorkday Thursday = ?printWorkday_rhs_4
printWorkday Friday = ?printWorkday_rhs_5

-- printWorkday Monday MondayW = "Monday"
-- printWorkday Tuesday TuesdayW = "Tuesday"
-- printWorkday Wednesday WednesdayW = "Wednesday"
-- printWorkday Thursday ThursdayW = "Thursday"
-- printWorkday Friday FridayW = "Friday"
