import Mathlib
import Submission.Work.BoseB4.Split_ann_excited
import Submission.Work.BoseB4.Split_inner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_excLift` — the condensate-free lift of a real excited state

`Work.BoseB4.split : RealFock m →ₗ[ℝ] (ℕ →₀ cfock (Excited m))` decomposes a
mode-lattice state into its condensate occupation `α 0` and its excited part
`α|₀`, with the Fock weight `√((α 0)! · α|₀!)`.  On the *condensate-free* sector
(`α 0 = 0`, i.e. `α = lift β` for an excited multi-index `β`) the weight is
`fockW 0 β = √(β!)`, so the image of `split` at level `0` is spanned, over `ℝ`,
by the canonical basis vectors `toCFock (Finsupp.single β 1)` of `cfock (Excited m)`.

Consequently every `w : cfock (Excited m)` whose canonical coordinates are **real**
— the hypothesis `hw` — is attained at condensate level `0`:

    `∃ f : RealFock m, split f = Finsupp.single 0 w`.

The lift used is `liftL`, the `ℝ`-linear "inverse" of `split` on that sector,

    `liftL g = Σ_β (g β / √(β!)) • x^{lift β}`   (`g : (Excited m →₀ ℕ) →₀ ℝ`),

whose normalisation `1 / fockW 0 β` exactly cancels the Fock weight of `split`.
The computational content is the pair of identities
`split_liftL : split ∘ liftL = levelL` and
`levelL_eq : levelL g = single 0 (toCFock (mapRange (↑) g))`,
`levelL` being the level-`0` placement of the complexified coefficient family.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option maxHeartbeats 4000000

namespace ExcLift

variable {m : ℕ} [NeZero m]

/-- The embedding of the excited modes into the mode lattice (`j ↦ ↑j`). -/
noncomputable def emb (m : ℕ) [NeZero m] : Excited m ↪ Fin m :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The lift of an excited multi-index to the condensate-free lattice multi-index
with the same occupation numbers. -/
noncomputable def lift (β : Excited m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.embDomain (emb m) β

lemma lift_apply_zero (β : Excited m →₀ ℕ) : lift β 0 = 0 := by
  rw [lift, Finsupp.embDomain_of_notMem_range]
  rintro ⟨a, ha⟩
  exact a.2 ha

lemma restOf_lift (β : Excited m →₀ ℕ) : restOf (lift β) = β := by
  ext j
  rw [restOf, Finsupp.subtypeDomain_apply, lift]
  exact Finsupp.embDomain_apply_self (emb m) β j

lemma mfacG_pos (β : Excited m →₀ ℕ) : 0 < mfacG β := by
  rw [mfacG]
  exact Finset.prod_pos (fun l _ => by positivity)

lemma fockW_zero_eq (β : Excited m →₀ ℕ) : fockW 0 β = Real.sqrt (mfacG β) := by
  simp [fockW]

lemma fockW_zero_ne (β : Excited m →₀ ℕ) : fockW 0 β ≠ 0 := by
  rw [fockW_zero_eq]
  exact ne_of_gt (Real.sqrt_pos.mpr (mfacG_pos β))

/-- A complex number with vanishing imaginary part is the real number `z.re`. -/
lemma ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z := by
  rw [← Complex.re_add_im z, h]
  simp

/-- A real scalar moves through `toCFock`; the `• 1` multiplies the coefficient. -/
lemma smul_toCFock_single (β : Excited m →₀ ℕ) (a : ℝ) :
    a • toCFock (Excited m) (Finsupp.single β 1)
      = toCFock (Excited m) (Finsupp.single β ((a : ℝ) : ℂ)) := by
  trans ((a : ℂ)) • toCFock (Excited m) (Finsupp.single β 1)
  · exact (Complex.coe_smul (E := ↥(cfock (Excited m))) a _).symm
  · rw [← map_smul, Finsupp.smul_single]
    simp

/-- The Fock weight `fockW 0 β = √(β!)` of `split` at condensate level `0` is
cancelled by the normalisation `1 / fockW 0 β`. -/
lemma one_div_fockW_smul (β : Excited m →₀ ℕ) :
    (1 / fockW 0 β) •
        toCFock (Excited m) (Finsupp.single β (((fockW 0 β : ℝ)) : ℂ))
      = toCFock (Excited m) (Finsupp.single β 1) := by
  trans (((1 / fockW 0 β : ℝ)) : ℂ) •
      toCFock (Excited m) (Finsupp.single β (((fockW 0 β : ℝ)) : ℂ))
  · exact (Complex.coe_smul (E := ↥(cfock (Excited m))) (1 / fockW 0 β) _).symm
  · rw [← map_smul, Finsupp.smul_single]
    have hscal : ((((1 / fockW 0 β : ℝ)) : ℂ)) * ((((fockW 0 β : ℝ)) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, show (1 / fockW 0 β) * fockW 0 β = 1 from
        one_div_mul_cancel (fockW_zero_ne β)]
      exact Complex.ofReal_one
    rw [smul_eq_mul, hscal]

/-- The level-0 "inverse" of `split`: from a real coefficient family `g` on the
excited multi-indices it builds the condensate-free lattice state
`Σ_β (g β / √(β!)) • x^{lift β}`. -/
noncomputable def liftL : ((Excited m →₀ ℕ) →₀ ℝ) →ₗ[ℝ] RealFock m :=
  Finsupp.lsum ℝ fun β =>
    LinearMap.toSpanSingleton ℝ (RealFock m)
      ((1 / fockW 0 β) • Finsupp.single (lift β) 1)

lemma liftL_single (β : Excited m →₀ ℕ) (a : ℝ) :
    liftL (Finsupp.single β a)
      = a • ((1 / fockW 0 β) • Finsupp.single (lift β) 1) := by
  rw [liftL, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

lemma split_single_lift (β : Excited m →₀ ℕ) :
    split (Finsupp.single (lift β) (1 / fockW 0 β))
      = Finsupp.single 0 (toCFock (Excited m) (Finsupp.single β 1)) := by
  rw [split_single_basis, splitVec, restOf_lift, lift_apply_zero]
  rw [Finsupp.smul_single]
  congr 1
  exact one_div_fockW_smul β

/-- The level-`0` target map: the complexification of the coefficient family,
placed at condensate level `0`. -/
noncomputable def levelL : ((Excited m →₀ ℕ) →₀ ℝ) →ₗ[ℝ] (ℕ →₀ cfock (Excited m)) :=
  Finsupp.lsum ℝ fun β =>
    LinearMap.toSpanSingleton ℝ (ℕ →₀ cfock (Excited m))
      (Finsupp.single 0 (toCFock (Excited m) (Finsupp.single β 1)))

/-- `split ∘ liftL` is the level-`0` placement of the coefficient family. -/
lemma split_liftL (g : (Excited m →₀ ℕ) →₀ ℝ) : split (liftL g) = levelL g := by
  induction g using Finsupp.induction_linear with
  | zero => simp [liftL, levelL]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single β a =>
      rw [liftL_single, levelL, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
        map_smul, map_smul, split_single_basis]
      rw [splitVec, restOf_lift, lift_apply_zero, Finsupp.smul_single, Finsupp.smul_single]
      simp only [one_smul]
      congr 2
      exact one_div_fockW_smul β

/-- `levelL` is the complexification of the coefficient family at level `0`. -/
lemma levelL_eq (g : (Excited m →₀ ℕ) →₀ ℝ) :
    levelL g = Finsupp.single 0 (toCFock (Excited m)
      (Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp) g)) := by
  induction g using Finsupp.induction_linear with
  | zero => simp [levelL]
  | add f g hf hg =>
      rw [map_add, hf, hg, Finsupp.mapRange_add (fun x y => by simp), map_add,
        Finsupp.single_add]
  | single β a =>
      rw [levelL, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
        Finsupp.mapRange_single, ← smul_toCFock_single β a, Finsupp.smul_single]

end ExcLift

open ExcLift

/-- **The condensate-free lift.**  Every `w` in the Fock space of the excited modes
whose canonical coordinates are real is the condensate-level-`0` part of a
mode-lattice state: `split f = Finsupp.single 0 w`. -/
theorem exists_excLift {m : ℕ} [NeZero m] (w : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hw : ∀ β : Work.BoseB4.Excited m →₀ ℕ,
      (((Work.BoseB4.toCFock (Work.BoseB4.Excited m)).symm w) β).im = 0) :
    ∃ f : Work.BoseB4.RealFock m, Work.BoseB4.split f = Finsupp.single 0 w := by
  let v : (Excited m →₀ ℕ) →₀ ℂ := (toCFock (Excited m)).symm w
  have hv : toCFock (Excited m) v = w := (toCFock (Excited m)).apply_symm_apply w
  have hw' : ∀ β : Excited m →₀ ℕ, (v β).im = 0 := hw
  refine ⟨liftL (v.mapRange Complex.re (by simp)), ?_⟩
  rw [split_liftL, levelL_eq]
  have hV : Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp)
      (v.mapRange Complex.re (by simp)) = v := by
    ext β
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact ofReal_re_of_im_zero (hw' β)
  rw [hV, hv]

end Work.BoseBoxFock
