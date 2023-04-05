-- https://hackage.haskell.org/package/logict-0.8.0.0/docs/Control-Monad-Logic-Class.html
class MonadLogic (m : Type → Type) where
  mzero : m α
  mplus : m α → m α → m α
  msplit : m α → m (Option (α × m α))

structure LogicT (m: Type → Type) (α : Type) : Type where 
  run : m (Array α)

abbrev LogicM (α : Type) := LogicT Id α

instance [Functor m] : Functor (LogicT m) where
  map f l := LogicT.mk <| (Array.map f) <$> l.run

instance [Monad m] : Monad (LogicT m) where 
  pure a := LogicT.mk <| pure #[a]
  bind ma a2mb := LogicT.mk do 
    let mut bs := #[]
    for a in (← ma.run) do
      bs := bs.append (← (a2mb a).run) 
    return bs

instance [Monad m] : MonadLogic (LogicT m) where
  mzero := LogicT.mk <| pure #[]
  mplus m1 m2 := LogicT.mk <| do return (← m1.run) ++ (← m2.run)
  msplit ma :=
    LogicT.mk do
      let arr ← ma.run
      match H : arr.size with 
      | 0 => pure #[Option.none]
      | n'+1 => do 
        let a := arr[0]'(by { simp[H, Nat.zero_lt_succ] })
        let as := LogicT.mk (pure arr[1:])
        pure #[.some (a, as)] -- laziness.

instance [Monad m] [MonadState σ m] : MonadState σ (LogicT m) where 
  get := LogicT.mk <| do let a ← get; return #[a] 
  set s := LogicT.mk <| do MonadState.set s; return #[()]
  modifyGet f := LogicT.mk <| do 
    let a ← MonadState.modifyGet f
    return #[a]

instance [Monad m] : MonadLift m (LogicT m) where 
  monadLift ma := LogicT.mk do return #[← ma]

#check MonadError
instance [MonadError m] : MonadError (LogicT m) where 

instance [MonadExceptOf ε m] [Monad m] : MonadExceptOf ε (LogicT m) where
  throw err := LogicT.mk (do throw err)
  tryCatch body handler := sorry -- TODO: think about this!
