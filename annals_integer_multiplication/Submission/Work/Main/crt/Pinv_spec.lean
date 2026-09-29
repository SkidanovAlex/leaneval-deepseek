import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pcr_inj

namespace Work.Main.crt

open Work.Main

/-- **The flat CRT reindexing `Pcr` is a bijection on `[0, ∏ss)`.** The map
`f : Fin ss.prod → Fin ss.prod`, `m ↦ Pcr ss m` is well defined since `Pcr ss m < ∏ss`
(`Pcr_lt`) and injective on `[0, ∏ss)` (`Pcr_inj`); a self-map of a finite type that is
injective is surjective, hence `Pcr ss` hits every `q < ∏ss`, and `Pinv ss q` -- the chosen
preimage -- is a preimage in `[0, ∏ss)`. -/
theorem Pinv_spec {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {q : ℕ} (hq : q < ss.prod) : Pinv ss q < ss.prod ∧ Pcr ss (Pinv ss q) = q := by
  have hex : ∃ m, m < ss.prod ∧ Pcr ss m = q := by
    let f : Fin ss.prod → Fin ss.prod := fun m => ⟨Pcr ss m.val, Pcr_lt hpos m.val⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      exact Pcr_inj hcop hpos a.isLt b.isLt (congrArg Fin.val hab)
    obtain ⟨m, hm⟩ := Finite.surjective_of_injective hf ⟨q, hq⟩
    exact ⟨m.val, m.isLt, by simpa [f] using congrArg Fin.val hm⟩
  have hpinv : Pinv ss q = hex.choose := by
    rw [Pinv]; exact dite_eq_left hex
  rw [hpinv]
  exact hex.choose_spec

end Work.Main.crt
