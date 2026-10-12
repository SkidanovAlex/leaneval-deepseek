import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7A.Est1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.Algebra` — the algebra of FS `eq:EstimateQ3Tilde1`

The operator algebra of the first estimate of FS `lem:EstimatesOnQ3-js`:

* the adjointness of `a`, `ã`, `b` in the Fock form, and the commutation
  relations of the θ-modes with `a, a†` (read off from `TildeData` by
  adjointness, `a_taDag_comm`, `taDag_a_comm`, …);
* the three **squeezed commutators** of `Est1.Defs` — `κA = [ã_{-s}†,b_k†]`
  (`kA_comm`), `κB = [ã_{-s}†,b_{s-k}†]` (`kB_comm`), `κC = [b_k†,b_{s-k}†]`
  (`kC_comm`), the last using `SubstHyp.hasKernel` — and their annihilation
  counterparts (`kA_comm'`, `kB_comm'`, `kC_comm'`, adjoints of the first
  three);
* the reindexing `(s,k) ↦ (-s,-k)` of the `(P_L × P_H)` sum
  (`sum_excited_PHset_neg`) and the invariance of the weight `γβ`
  (`gA_bA_neg`);
* the two **word identities** `word_cre`, `word_ann` (FS's rewriting of the
  `b†b†`/`bb` halves of `Q₃⁽¹⁾`, i.e. his `T₁(k)` plus the comm part of `T₂`).

Everything here is `sorry`-free; the decomposition theorem
`Q3oneT = Σ_k (b_k†Y_k + Y_k†b_k) + R1` itself is the next step
(`Est1.Skeleton`, delegated).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode}

theorem bp_ext (X Y : F.H →ₗ[ℝ] F.H) (h : ∀ f g : F.H, F.bp (X f) g = F.bp (Y f) g) :
    X = Y := by
  ext f
  have h0 : F.bp ((X - Y) f) ((X - Y) f)
      = F.bp (X f) ((X - Y) f) - F.bp (Y f) ((X - Y) f) := by
    simp only [LinearMap.sub_apply, map_sub]
    ring
  have h1 : F.bp ((X - Y) f) ((X - Y) f) = 0 := by rw [h0, h f ((X - Y) f), sub_self]
  exact sub_eq_zero.mp (F.bp_def ((X - Y) f) h1)

theorem bp_a_left (i : Mode) (f g : F.H) :
    F.bp (F.a i f) g = F.bp f (F.aDag i g) := by
  rw [F.bp_symm (F.a i f) g, ← F.aDag_adjoint i g f, F.bp_symm (F.aDag i g) f]

theorem bp_aDag_left (i : Mode) (f g : F.H) :
    F.bp (F.aDag i f) g = F.bp f (F.a i g) := F.aDag_adjoint i f g

theorem bp_taDag_left (T : TildeData F) (s : Mode) (f g : F.H) :
    F.bp (T.taDag s f) g = F.bp f (T.ta s g) := T.taDag_adjoint s f g

theorem bp_ta_left (T : TildeData F) (s : Mode) (f g : F.H) :
    F.bp (T.ta s f) g = F.bp f (T.taDag s g) := by
  rw [F.bp_symm (T.ta s f) g, ← T.taDag_adjoint s g f, F.bp_symm (T.taDag s g) f]

/-- The adjointness of `b_k`: `⟨b_k f, g⟩ = ⟨f, b_k† g⟩`. -/
theorem bp_bOp_left (E : Q3Env Mode) (i : Mode) (f g : F.H) :
    F.bp (F.bOp E.alpha i f) g = F.bp f (F.bOpDag E.alpha i g) := by
  rw [FockData.bOp, FockData.bOpDag]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul,
    bp_a_left, bp_aDag_left]

/-- The adjointness of `b_k†`. -/
theorem bp_bOpDag_left (E : Q3Env Mode) (i : Mode) (f g : F.H) :
    F.bp (F.bOpDag E.alpha i f) g = F.bp f (F.bOp E.alpha i g) := by
  rw [FockData.bOp, FockData.bOpDag]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul,
    bp_aDag_left, bp_a_left]

/-- The normalised shape of the two sides: all operators pushed into the second
slot. -/
macro "bp_norm" : tactic => `(tactic|
  (simp only [FockData.bOpDag, FockData.bOp, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul,
    smul_eq_mul, bp_taDag_left, bp_ta_left, bp_a_left, bp_aDag_left,
    bp_bOp_left, bp_bOpDag_left]))

/-- `ã_s† a_k = a_k ã_s† - ccrX s k`. -/
theorem taDag_a_comm (T : TildeData F) (s k : Mode) :
    T.taDag s ∘ₗ F.a k = F.a k ∘ₗ T.taDag s - (T.ccrX s k) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  bp_norm
  have hpt : T.ta s (F.aDag k g) = F.aDag k (T.ta s g) + (T.ccrX s k) • g := by
    have := LinearMap.congr_fun (T.ta_aDag s k) g
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  rw [hpt]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- `a_k ã_s† = ã_s† a_k + ccrX s k`. -/
theorem a_taDag_comm (T : TildeData F) (k s : Mode) :
    F.a k ∘ₗ T.taDag s = T.taDag s ∘ₗ F.a k + (T.ccrX s k) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h := taDag_a_comm T s k
  rw [h]
  module

/-- `[ã_{-s}†, b_k†] = κA_{sk}`. -/
theorem kA_comm (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    T.taDag (-s) ∘ₗ F.bOpDag E.alpha k
      = F.bOpDag E.alpha k ∘ₗ T.taDag (-s) + (kA T E s k) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  bp_norm
  have h1 : T.ta (-s) (F.a k g) = F.a k (T.ta (-s) g) := by
    have := LinearMap.congr_fun (T.ta_a_comm (-s) k) g
    simpa only [LinearMap.comp_apply] using this
  have h2 : T.ta (-s) (F.aDag (-k) g)
      = F.aDag (-k) (T.ta (-s) g) + (T.ccrX (-s) (-k)) • g := by
    have := LinearMap.congr_fun (T.ta_aDag (-s) (-k)) g
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  rw [h1, h2, kA]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- `[ã_{-s}†, b_{s-k}†] = κB_{sk}`. -/
theorem kB_comm (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    T.taDag (-s) ∘ₗ F.bOpDag E.alpha (s - k)
      = F.bOpDag E.alpha (s - k) ∘ₗ T.taDag (-s) + (kB T E s k) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  bp_norm
  have h1 : T.ta (-s) (F.a (s - k) g) = F.a (s - k) (T.ta (-s) g) := by
    have := LinearMap.congr_fun (T.ta_a_comm (-s) (s - k)) g
    simpa only [LinearMap.comp_apply] using this
  have h2 : T.ta (-s) (F.aDag (-(s - k)) g)
      = F.aDag (-(s - k)) (T.ta (-s) g) + (T.ccrX (-s) (-(s - k))) • g := by
    have := LinearMap.congr_fun (T.ta_aDag (-s) (-(s - k))) g
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  rw [h1, h2, show -(s - k) = k - s by abel, kB]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- `[b_k†, b_{s-k}†] = κC_{sk}` (FS `σ₂`). -/
theorem kC_comm (T : TildeData F) (E : Q3Env Mode) (h : SubstHyp F T E) (s k : Mode) :
    F.bOpDag E.alpha k ∘ₗ F.bOpDag E.alpha (s - k)
      = F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k
        + (kC E s k) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  bp_norm
  have S1 : F.a (s - k) (F.a k g) = F.a k (F.a (s - k) g) := by
    have := LinearMap.congr_fun (F.ann_comm k (s - k)) g
    simpa only [LinearMap.comp_apply] using this.symm
  have S2 : F.aDag (-(s - k)) (F.a k g)
      = F.a k (F.aDag (-(s - k)) g) - (F.ccrK k (-(s - k))) • g := by
    have := LinearMap.congr_fun (F.ccr k (-(s - k))) g
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; module
  have S3 : F.a (s - k) (F.aDag (-k) g)
      = F.aDag (-k) (F.a (s - k) g) + (F.ccrK (s - k) (-k)) • g := by
    have := LinearMap.congr_fun (F.ccr (s - k) (-k)) g
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  have S4 : F.aDag (-(s - k)) (F.aDag (-k) g) = F.aDag (-k) (F.aDag (-(s - k)) g) := by
    have := LinearMap.congr_fun (F.cre_comm (-k) (-(s - k))) g
    simpa only [LinearMap.comp_apply] using this.symm
  rw [S1, S2, S3, S4]
  have e1 : F.ccrK (s - k) (-k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
    rw [h.hasKernel (s - k) (-k), show (s - k) - (-k) = s by abel, h.hatChi_even k]
    ring
  have e2 : F.ccrK k (-(s - k)) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
    rw [h.hasKernel k (-(s - k)), show k - (-(s - k)) = s by abel, h.hatChi_even (s - k)]
  rw [e1, e2, kC]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring_nf

/-- `[ã_{-s}, b_k] = -κA_{sk}`: the adjoint of `kA_comm`. -/
theorem kA_comm' (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    T.ta (-s) ∘ₗ F.bOp E.alpha k
      = F.bOp E.alpha k ∘ₗ T.ta (-s) + (-(kA T E s k)) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_smul, smul_eq_mul, bp_ta_left, bp_bOp_left]
  have h := LinearMap.congr_fun (kA_comm T E s k) g
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rw [h]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- `[ã_{-s}, b_{s-k}] = -κB_{sk}`: the adjoint of `kB_comm`. -/
theorem kB_comm' (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    T.ta (-s) ∘ₗ F.bOp E.alpha (s - k)
      = F.bOp E.alpha (s - k) ∘ₗ T.ta (-s) + (-(kB T E s k)) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_smul, smul_eq_mul, bp_ta_left, bp_bOp_left]
  have h := LinearMap.congr_fun (kB_comm T E s k) g
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rw [h]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- `[b_k, b_{s-k}] = -κC_{sk}`: the adjoint of `kC_comm`. -/
theorem kC_comm' (T : TildeData F) (E : Q3Env Mode) (h : SubstHyp F T E) (s k : Mode) :
    F.bOp E.alpha k ∘ₗ F.bOp E.alpha (s - k)
      = F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k
        + (-(kC E s k)) • (1 : F.H →ₗ[ℝ] F.H) := by
  refine bp_ext _ _ fun f g => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_add, map_smul, smul_eq_mul, bp_bOp_left]
  have hh := LinearMap.congr_fun (kC_comm T E h s k) g
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hh
  rw [hh]
  simp only [map_add, map_smul, smul_eq_mul]
  ring


section Decomp

variable (T : TildeData F) (E : Q3Env Mode) (h : SubstHyp F T E)

/-- Composition with a finite sum of linear maps. -/
theorem comp_sum_lm {ι : Type*} (f : F.H →ₗ[ℝ] F.H) (s : Finset ι)
    (g : ι → F.H →ₗ[ℝ] F.H) :
    f ∘ₗ (∑ i ∈ s, g i) = ∑ i ∈ s, f ∘ₗ g i := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-- Composition on the right with a finite sum of linear maps. -/
theorem sum_comp_lm {ι : Type*} (s : Finset ι) (g : ι → F.H →ₗ[ℝ] F.H)
    (f : F.H →ₗ[ℝ] F.H) :
    (∑ i ∈ s, g i) ∘ₗ f = ∑ i ∈ s, (g i ∘ₗ f) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, Finset.sum_apply]

/-- The excited modes are invariant under negation. -/
theorem mem_excited_neg (i : Mode) : (-i ∈ excited Mode) ↔ (i ∈ excited Mode) := by
  simp only [Work.BoseB7.excited, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro hi hi'; exact hi (by rw [hi', neg_zero])
  · intro hi hi'; exact hi (neg_eq_zero.mp hi')

/-- The reindexing `(s,k) ↦ (-s,-k)` of a double sum over `excited × P_H`. -/
theorem sum_excited_PHset_neg {M : Type*} [AddCommMonoid M] (g : Mode → Mode → M) :
    (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, g (-s) (-k))
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, g s k := by
  have h1 : ∀ s : Mode, (∑ k ∈ F.PHset E, g (-s) (-k)) = ∑ k ∈ F.PHset E, g (-s) k :=
    fun s => Finset.sum_equiv (Equiv.neg Mode) (fun i => mem_PHset_neg F E i)
      (fun i _ => rfl)
  have h2 : (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, g (-s) (-k))
      = ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, g (-s) k :=
    Finset.sum_congr rfl (fun s _ => h1 s)
  rw [h2]
  exact Finset.sum_equiv (Equiv.neg Mode) (fun i => (mem_excited_neg i).symm) (fun i _ => rfl)

/-- The weight `γβ` is invariant under `(s,k) ↦ (-s,-k)`. -/
theorem gA_bA_neg (hfL : ∀ s : Mode, E.fL (-s) = E.fL s)
    (hW1 : ∀ s : Mode, E.W1 (-s) = E.W1 s)
    (hα : ∀ s : Mode, E.alpha (-s) = E.alpha s) (s k : Mode) :
    gA E (-s) (-k) * bA E (-s) (-k) = gA E s k * bA E s k := by
  simp only [gA, bA, Q3Env.q3Denom, hfL, hW1, hα, show -s - -k = -(s - k) by abel]

/-- `Q1b(-s,-k)` is FS's reindexed `b†b†` word. -/
theorem Q1b_neg (s k : Mode) :
    Q1b F T E (-s) (-k)
      = T.taDag (-s) ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k) := by
  simp only [Q1b, show -k - -s = s - k by abel, neg_neg]

/-- `Q1bDag(-s,-k)` is FS's reindexed `bb` word. -/
theorem Q1bDag_neg (s k : Mode) :
    Q1bDag F T E (-s) (-k)
      = F.bOp E.alpha k ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ T.ta (-s)) := by
  simp only [Q1bDag, show -k - -s = s - k by abel, neg_neg]

/-- The `b†b†` word identity: the commutator expansion of FS's `T₂,comm`. -/
theorem word_cre (h : SubstHyp F T E) (s k : Mode) :
    T.taDag (-s) ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ F.bOpDag E.alpha k)
      = S1 F T E s k + (kB T E s k) • F.bOpDag E.alpha k
        + (kA T E s k) • F.bOpDag E.alpha (s - k) - (kC E s k) • T.taDag (-s) := by
  ext x
  simp only [S1, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  have hY : T.taDag (-s) (F.bOpDag E.alpha (s - k) (F.bOpDag E.alpha k x))
      = F.bOpDag E.alpha (s - k) (T.taDag (-s) (F.bOpDag E.alpha k x))
        + (kB T E s k) • (F.bOpDag E.alpha k x) := by
    have := LinearMap.congr_fun (kB_comm T E s k) (F.bOpDag E.alpha k x)
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  have hX : T.taDag (-s) (F.bOpDag E.alpha k x)
      = F.bOpDag E.alpha k (T.taDag (-s) x) + (kA T E s k) • x := by
    have := LinearMap.congr_fun (kA_comm T E s k) x
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using this
  have hZ : F.bOpDag E.alpha (s - k) (F.bOpDag E.alpha k (T.taDag (-s) x))
      = F.bOpDag E.alpha k (F.bOpDag E.alpha (s - k) (T.taDag (-s) x))
        - (kC E s k) • (T.taDag (-s) x) := by
    have := LinearMap.congr_fun (kC_comm T E h s k) (T.taDag (-s) x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; module
  rw [hY, hX]
  simp only [map_add, map_smul]
  rw [hZ]
  module

/-- The `bb` word identity. -/
theorem word_ann (h : SubstHyp F T E) (s k : Mode) :
    F.bOp E.alpha k ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ T.ta (-s))
      = S2 F T E s k + (kB T E s k) • F.bOp E.alpha k
        + (kA T E s k) • F.bOp E.alpha (s - k) - (kC E s k) • T.ta (-s) := by
  ext x
  simp only [S2, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  have hY : T.ta (-s) (F.bOp E.alpha (s - k) (F.bOp E.alpha k x))
      = F.bOp E.alpha (s - k) (T.ta (-s) (F.bOp E.alpha k x))
        - (kB T E s k) • (F.bOp E.alpha k x) := by
    have := LinearMap.congr_fun (kB_comm' T E s k) (F.bOp E.alpha k x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; module
  have hX : T.ta (-s) (F.bOp E.alpha k x)
      = F.bOp E.alpha k (T.ta (-s) x) - (kA T E s k) • x := by
    have := LinearMap.congr_fun (kA_comm' T E s k) x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; module
  have hZ : F.bOp E.alpha (s - k) (F.bOp E.alpha k (T.ta (-s) x) - (kA T E s k) • x)
      = F.bOp E.alpha k (F.bOp E.alpha (s - k) (T.ta (-s) x))
        + (kC E s k) • (T.ta (-s) x) - (kA T E s k) • (F.bOp E.alpha (s - k) x) := by
    rw [map_sub, map_smul]
    have := LinearMap.congr_fun (kC_comm' T E h s k) (T.ta (-s) x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    rw [this]; module
  rw [hY, hX, hZ]
  module

end Decomp

end Est1

end Work.BoseB7A
