import Mathlib
import Submission.Work.Resample.buQWkey

namespace Work.Resample

/-- The key map `egLam s t` is a left inverse of the fused index map `egNu s t` on `Fin s`,
characterises the selected indices by `egLam s t i < s`, and is injective on `{0,…,t-1}`
(so its image list has no duplicates).  All three facts are immediate consequences of
`Work.Resample.buQWkey`. -/
theorem buKeysSpec (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) :
    (∀ ℓ : Fin s, Work.Resample.egLam s t (Work.Resample.egNu s t (ℓ : ℕ)) = (ℓ : ℕ)) ∧
    (∀ i < t, Work.Resample.egLam s t i < s ↔ ∃ ℓ : Fin s, Work.Resample.egNu s t (ℓ : ℕ) = i) ∧
    (List.ofFn (fun i : Fin t => ((Work.Resample.egLam s t i : ℕ) : ℤ))).Nodup := by
  obtain ⟨-, -, hleft, hlt, -, hnodup, -, -, -⟩ := buQWkey s t hs hst hcop
  exact ⟨fun ℓ => hleft _ ℓ rfl, hlt, hnodup⟩

end Work.Resample
