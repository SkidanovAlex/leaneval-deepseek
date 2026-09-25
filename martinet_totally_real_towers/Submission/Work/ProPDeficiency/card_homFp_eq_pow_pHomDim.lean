import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank

namespace Work.ProPDeficiency

set_option linter.style.haveILetI false

-- File: Submission/Work/ProPDeficiency/card_homFp_eq_pow_pHomDim.lean, namespace `Work.ProPDeficiency`.
-- `HomFp p G := G →* Multiplicative (ZMod p)` and `pHomDim p G := Nat.log p (Nat.card (HomFp p G))`
-- are defined in `Submission.Work.ProPDeficiency.HomRank`.
-- Content: for `G` finitely generated and `p` PRIME, `Hom(G, 𝔽_p)` is finite of `p`-power order,
-- so `Nat.card = p ^ pHomDim`.  (Primeness is needed: `p = 4`, `G = Multiplicative (ZMod 2)` has
-- `Nat.card HomFp = 2` but `Nat.log 4 2 = 0`.)
-- Proof: finiteness from the injection `HomFp p G ↪ (Fin n → Multiplicative (ZMod p))` for a
-- finite generating family `Fin n → G` (`Group.fg_iff_nonempty_finite_generators`, with agreement
-- on a generating family giving equality of homs via `Group.Generators.hom_ext`); then
-- `IsPGroup p (HomFp p G)` because `φ ^ p = 1` pointwise (`Multiplicative (ZMod p)` has exponent
-- `p`, via `ofAdd_nsmul`), and `IsPGroup.iff_card` gives `Nat.card = p ^ k`; finally `Nat.log_pow`.

/-- For `G` finitely generated and `p` prime, `Hom(G, 𝔽_p)` is a finite `p`-group, hence
`Nat.card (HomFp p G) = p ^ pHomDim p G`. -/
theorem card_homFp_eq_pow_pHomDim {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Group.FG G] :
    Nat.card (HomFp p G) = p ^ pHomDim p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG G)
  -- Every element of `Multiplicative (ZMod p)` has `p`-th power `1`.
  have hpow : ∀ x : Multiplicative (ZMod p), x ^ p = 1 := by
    intro x
    rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  -- `HomFp p G` has exponent dividing `p`, pointwise.
  have hExp : ∀ φ : HomFp p G, φ ^ p = 1 := by
    intro φ
    ext g
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    exact hpow (φ g)
  have hP : IsPGroup p (HomFp p G) := fun φ => ⟨1, by simpa using hExp φ⟩
  -- A hom out of `G` is determined by its values on a generating family, so `HomFp p G` is finite.
  haveI : Finite (HomFp p G) := by
    refine @Finite.of_injective _ _ ?_ (fun φ : HomFp p G => fun i : Fin n => φ (P.val i))
      (fun φ ψ h => P.hom_ext φ ψ (fun i => congr_fun h i))
    exact Pi.finite
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk, pHomDim, hk, Nat.log_pow hp.one_lt]

end Work.ProPDeficiency
