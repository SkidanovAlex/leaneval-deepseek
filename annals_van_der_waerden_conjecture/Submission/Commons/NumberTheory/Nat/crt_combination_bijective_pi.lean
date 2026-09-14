import Mathlib
import Submission.Commons.NumberTheory.Nat.crt_combination_bijective

open scoped BigOperators

namespace Commons.NumberTheory.Nat

/-- Pointwise CRT combination: this is exactly the map whose bijectivity is
`crt_combination_bijective`. -/
private noncomputable def crtComb (s : Finset ℕ) :
    (∀ m : {m // m ∈ s}, ZMod (m : ℕ)) → ZMod (∏ m ∈ s, m) :=
  fun a => ∑ m : {m // m ∈ s},
    (((a m).val : ℕ) : ZMod (∏ m ∈ s, m)) *
      (((∏ m ∈ s, m) / (m : ℕ) : ℕ) : ZMod (∏ m ∈ s, m))

theorem crt_combination_bijective_pi (s : Finset ℕ) (hpos : ∀ m ∈ s, 0 < m)
    (hcop : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' → Nat.Coprime m m') (n : ℕ) :
    Function.Bijective (fun b : (∀ m : {m // m ∈ s}, Fin n → ZMod (m : ℕ)) =>
      fun i : Fin n => ∑ m : {m // m ∈ s},
        (((b m i).val : ℕ) : ZMod (∏ m ∈ s, m)) *
          (((∏ m ∈ s, m) / (m : ℕ) : ℕ) : ZMod (∏ m ∈ s, m))) := by
  classical
  have hG : Function.Bijective (crtComb s) := crt_combination_bijective s hpos hcop
  change Function.Bijective
    (fun b : (∀ m : {m // m ∈ s}, Fin n → ZMod (m : ℕ)) =>
      fun i : Fin n => crtComb s (fun m => b m i))
  refine ⟨?_, ?_⟩
  · intro b b' hbb'
    funext m i
    have h := congr_fun hbb' i
    exact congr_fun (hG.1 h) m
  · intro y
    choose a ha using fun i => hG.2 (y i)
    refine ⟨fun m i => a i m, ?_⟩
    funext i
    show crtComb s (a i) = y i
    exact ha i

end Commons.NumberTheory.Nat
