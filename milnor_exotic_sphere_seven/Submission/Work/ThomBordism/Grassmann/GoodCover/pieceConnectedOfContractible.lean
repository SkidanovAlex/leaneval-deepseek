import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.Defs
import Submission.Work.ThomBordism.Grassmann.twoSetConnected
import Submission.Work.ThomBordism.Grassmann.Torsion.annulusGeom
import Submission.Work.ThomBordism.Grassmann.GoodCover.PiZeroAux
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.ThomBordism.Grassmann.exists_homeo_nuDisc
import Submission.Work.ThomBordism.Grassmann.finsetCoveredConnected
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.Stems.homotopyGroup_prod
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology unitInterval
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann.GoodCover


open Work.ThomBordism.TwoSet

noncomputable section

variable {k m : ℕ}

/-! ## Preliminaries -/

/-- Triviality of `π₀` of a path-connected space. -/
theorem subsingleton_piZero_of_pathConnected {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) := by
  haveI : Subsingleton (ZerothHomotopy X) := inferInstance
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective
    (Subsingleton.elim _ _)⟩

/-! ## Arithmetic for the radial homotopies -/

/-- The radial coefficient `2/(t+1)`. -/
def shellCoef (t : ℝ) : ℝ := 2 / (t + 1)

/-- The interpolation coefficient `(1-s)·2/(t+1) + s`. -/
def shellAlpha (s t : ℝ) : ℝ := (1 - s) * shellCoef t + s

theorem shellCoef_pos {t : ℝ} (ht : 0 ≤ t) : 0 < shellCoef t := by
  unfold shellCoef
  exact div_pos (by norm_num) (by linarith)

theorem one_lt_shellCoef_mul {t : ℝ} (ht : 1 < t) : 1 < shellCoef t * t := by
  unfold shellCoef
  rw [div_mul_eq_mul_div, one_lt_div (by linarith)]
  linarith

theorem shellCoef_mul_lt_two {t : ℝ} (ht : 1 < t) : shellCoef t * t < 2 := by
  unfold shellCoef
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  linarith

theorem shellAlpha_zero (t : ℝ) : shellAlpha 0 t = shellCoef t := by
  unfold shellAlpha; ring

theorem shellAlpha_one (t : ℝ) : shellAlpha 1 t = 1 := by
  unfold shellAlpha; ring

theorem one_lt_shellAlpha_mul (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 1 < t) :
    1 < shellAlpha s t * t := by
  have h : shellAlpha s t * t = (1 - s) * (shellCoef t * t) + s * t := by
    unfold shellAlpha; ring
  rw [h]
  have hc : 1 < shellCoef t * t := one_lt_shellCoef_mul ht
  rcases lt_or_eq_of_le hs1 with hlt | heq
  · have h1 : (1 - s) * 1 < (1 - s) * (shellCoef t * t) :=
      mul_lt_mul_of_pos_left hc (by linarith)
    have h2 : s * 1 ≤ s * t := mul_le_mul_of_nonneg_left (le_of_lt ht) hs0
    linarith
  · subst heq
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, zero_mul, zero_add, one_mul]
    exact ht

theorem shellAlpha_mul_lt_two (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht1 : 1 < t) (ht2 : t < 2) :
    shellAlpha s t * t < 2 := by
  have h : shellAlpha s t * t = (1 - s) * (shellCoef t * t) + s * t := by
    unfold shellAlpha; ring
  rw [h]
  have hc : shellCoef t * t < 2 := shellCoef_mul_lt_two ht1
  rcases lt_or_eq_of_le hs1 with hlt | heq
  · have h1 : (1 - s) * (shellCoef t * t) < (1 - s) * 2 :=
      mul_lt_mul_of_pos_left hc (by linarith)
    have h2 : s * t ≤ s * 2 := mul_le_mul_of_nonneg_left (le_of_lt ht2) hs0
    have hsum : (1 - s) * 2 + s * 2 = 2 := by ring
    linarith
  · subst heq
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, zero_mul, zero_add, one_mul]
    exact ht2

theorem one_le_shellAlpha (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 1 < t) :
    0 < shellAlpha s t := by
  have hc : 0 < shellCoef t := shellCoef_pos (by linarith : (0 : ℝ) ≤ t)
  rcases lt_or_eq_of_le hs1 with hlt | heq
  · have h1 : 0 < (1 - s) * shellCoef t := mul_pos (by linarith) hc
    unfold shellAlpha
    linarith
  · subst heq
    unfold shellAlpha
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, zero_mul, zero_add]
    norm_num

/-! ## The shell over `U` and the radial homotopy equivalence with the annulus -/

/-- The "shell" `{fibN > 1}` of the total space over `U`. -/
def shellOver (k m : ℕ) (U : Set (OG k m)) : Set (Torsion.TM k m) :=
  {p : Torsion.TM k m | 1 < Torsion.fibN k m p ∧ p.1 ∈ U}

theorem annOver_subset_shellOver (k m : ℕ) (U : Set (OG k m)) :
    Torsion.annOver k m U ⊆ shellOver k m U := fun _ hp => ⟨hp.1, hp.2.2⟩

/-- The radial collapse `p ↦ (2/(fibN p + 1)) • p` of the shell onto the annulus. -/
def shellToAnn (k m : ℕ) (U : Set (OG k m)) : C(↥(shellOver k m U), ↥(Torsion.annOver k m U)) where
  toFun p :=
    ⟨Torsion.fibScale (shellCoef (Torsion.fibN k m p.1)) p.1, by
      have ht : 1 < Torsion.fibN k m p.1 := p.2.1
      have hnn : 0 ≤ shellCoef (Torsion.fibN k m p.1) := le_of_lt (shellCoef_pos (by linarith : (0 : ℝ) ≤ Torsion.fibN k m p.1))
      have hval := Torsion.fibN_fibScale (k := k) (m := m) hnn p.1
      exact ⟨lt_of_lt_of_eq (one_lt_shellCoef_mul ht) hval.symm,
        lt_of_eq_of_lt hval (shellCoef_mul_lt_two ht), p.2.2⟩⟩
  continuous_toFun := by
    have hc : Continuous fun p : ↥(shellOver k m U) => shellCoef (Torsion.fibN k m p.1) := by
      refine Continuous.div continuous_const
        (((Torsion.fibN_continuous k m).comp continuous_subtype_val).add continuous_const) ?_
      intro p
      have hp := p.2.1
      show Torsion.fibN k m p.1 + 1 ≠ 0
      linarith
    have hsm : Continuous fun p : ↥(shellOver k m U) =>
        (⟨p.1.1, shellCoef (Torsion.fibN k m p.1) • p.1.2⟩ : Torsion.TM k m) :=
      Work.Thom.continuous_smul_section (tautologicalBundle k m)
        ⟨fun p : ↥(shellOver k m U) => p.1, continuous_subtype_val⟩
        ⟨fun p => shellCoef (Torsion.fibN k m p.1), hc⟩
    exact hsm.subtype_mk _

/-- The inclusion of the annulus into the shell. -/
def annToShell (k m : ℕ) (U : Set (OG k m)) : C(↥(Torsion.annOver k m U), ↥(shellOver k m U)) where
  toFun p := ⟨p.1, ⟨p.2.1, p.2.2.2⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The radial homotopy on the shell, from `annToShell ∘ shellToAnn` to the identity. -/
def shellHom (k m : ℕ) (U : Set (OG k m)) : C(I × ↥(shellOver k m U), ↥(shellOver k m U)) where
  toFun q :=
    ⟨Torsion.fibScale (shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1)) q.2.1, by
      have ht : 1 < Torsion.fibN k m q.2.1 := q.2.2.1
      have hnn : 0 ≤ shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) :=
        le_of_lt (one_le_shellAlpha (q.1 : ℝ) _ q.1.2.1 q.1.2.2 ht)
      have hval := Torsion.fibN_fibScale (k := k) (m := m) hnn q.2.1
      exact ⟨lt_of_lt_of_eq
        (one_lt_shellAlpha_mul (q.1 : ℝ) _ q.1.2.1 q.1.2.2 ht) hval.symm, q.2.2.2⟩⟩
  continuous_toFun := by
    have hfib : Continuous fun q : I × ↥(shellOver k m U) => Torsion.fibN k m q.2.1 :=
      (Torsion.fibN_continuous k m).comp (continuous_subtype_val.comp continuous_snd)
    have hs : Continuous fun q : I × ↥(shellOver k m U) => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hc : Continuous fun q : I × ↥(shellOver k m U) =>
        shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) := by
      unfold shellAlpha
      refine ((continuous_const.sub hs).mul ?_).add hs
      refine Continuous.div continuous_const (hfib.add continuous_const) ?_
      intro q
      have hq := q.2.2.1
      show Torsion.fibN k m q.2.1 + 1 ≠ 0
      linarith
    have hsm : Continuous fun q : I × ↥(shellOver k m U) =>
        (⟨q.2.1.1, shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) • q.2.1.2⟩ : Torsion.TM k m) :=
      Work.Thom.continuous_smul_section (tautologicalBundle k m)
        ⟨fun q : I × ↥(shellOver k m U) => q.2.1, continuous_subtype_val.comp continuous_snd⟩
        ⟨fun q => shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1), hc⟩
    exact hsm.subtype_mk _

/-- The radial homotopy on the annulus, from `shellToAnn ∘ annToShell` to the identity. -/
def annHom (k m : ℕ) (U : Set (OG k m)) :
    C(I × ↥(Torsion.annOver k m U), ↥(Torsion.annOver k m U)) where
  toFun q :=
    ⟨Torsion.fibScale (shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1)) q.2.1, by
      have ht1 : 1 < Torsion.fibN k m q.2.1 := q.2.2.1
      have ht2 : Torsion.fibN k m q.2.1 < 2 := q.2.2.2.1
      have hnn : 0 ≤ shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) :=
        le_of_lt (one_le_shellAlpha (q.1 : ℝ) _ q.1.2.1 q.1.2.2 ht1)
      have hval := Torsion.fibN_fibScale (k := k) (m := m) hnn q.2.1
      exact ⟨lt_of_lt_of_eq
          (one_lt_shellAlpha_mul (q.1 : ℝ) _ q.1.2.1 q.1.2.2 ht1) hval.symm,
        lt_of_eq_of_lt hval (shellAlpha_mul_lt_two (q.1 : ℝ) _ q.1.2.1 q.1.2.2 ht1 ht2),
        q.2.2.2.2⟩⟩
  continuous_toFun := by
    have hfib : Continuous fun q : I × ↥(Torsion.annOver k m U) => Torsion.fibN k m q.2.1 :=
      (Torsion.fibN_continuous k m).comp (continuous_subtype_val.comp continuous_snd)
    have hs : Continuous fun q : I × ↥(Torsion.annOver k m U) => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hc : Continuous fun q : I × ↥(Torsion.annOver k m U) =>
        shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) := by
      unfold shellAlpha
      refine ((continuous_const.sub hs).mul ?_).add hs
      refine Continuous.div continuous_const (hfib.add continuous_const) ?_
      intro q
      have hq := q.2.2.1
      show Torsion.fibN k m q.2.1 + 1 ≠ 0
      linarith
    have hsm : Continuous fun q : I × ↥(Torsion.annOver k m U) =>
        (⟨q.2.1.1, shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1) • q.2.1.2⟩ : Torsion.TM k m) :=
      Work.Thom.continuous_smul_section (tautologicalBundle k m)
        ⟨fun q : I × ↥(Torsion.annOver k m U) => q.2.1, continuous_subtype_val.comp continuous_snd⟩
        ⟨fun q => shellAlpha (q.1 : ℝ) (Torsion.fibN k m q.2.1), hc⟩
    exact hsm.subtype_mk _

/-- The radial homotopy equivalence of the shell over `U` with the annulus over `U`. -/
noncomputable def shellHomotopyEquiv (k m : ℕ) (U : Set (OG k m)) :
    ContinuousMap.HomotopyEquiv ↥(shellOver k m U) ↥(Torsion.annOver k m U) :=
  ContinuousMap.HomotopyEquiv.mk (shellToAnn k m U) (annToShell k m U)
    ⟨ContinuousMap.Homotopy.mk (shellHom k m U)
      (fun p => by
        refine Subtype.ext ?_
        show Torsion.fibScale (shellAlpha (0 : ℝ) (Torsion.fibN k m p.1)) p.1
          = Torsion.fibScale (shellCoef (Torsion.fibN k m p.1)) p.1
        rw [shellAlpha_zero])
      (fun p => by
        refine Subtype.ext ?_
        show Torsion.fibScale (shellAlpha (1 : ℝ) (Torsion.fibN k m p.1)) p.1 = p.1
        rw [shellAlpha_one]
        exact Torsion.fibScale_one p.1)⟩
    ⟨ContinuousMap.Homotopy.mk (annHom k m U)
      (fun p => by
        refine Subtype.ext ?_
        show Torsion.fibScale (shellAlpha (0 : ℝ) (Torsion.fibN k m p.1)) p.1
          = Torsion.fibScale (shellCoef (Torsion.fibN k m p.1)) p.1
        rw [shellAlpha_zero])
      (fun p => by
        refine Subtype.ext ?_
        show Torsion.fibScale (shellAlpha (1 : ℝ) (Torsion.fibN k m p.1)) p.1 = p.1
        rw [shellAlpha_one]
        exact Torsion.fibScale_one p.1)⟩

/-! ## Triviality of the homotopy groups of the shell -/

theorem subsingleton_shellOver_of_annOver (k m : ℕ) (U : Set (OG k m)) {j : ℕ}
    (h : ∀ y : ↥(Torsion.annOver k m U),
      Subsingleton (HomotopyGroup (Fin j) ↥(Torsion.annOver k m U) y))
    (x : ↥(shellOver k m U)) :
    Subsingleton (HomotopyGroup (Fin j) ↥(shellOver k m U) x) := by
  haveI : DecidableEq (Fin j) := inferInstance
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    exact subsingleton_piZero_of_homotopyEquiv' (shellHomotopyEquiv k m U) (h _)
  · haveI : Nonempty (Fin j) := ⟨⟨0, hpos⟩⟩
    obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j) (shellHomotopyEquiv k m U) x
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-! ## Triviality of the homotopy groups of the annulus -/

theorem subsingleton_sphere_amb (k : ℕ) {j : ℕ} (hj : j < k - 1)
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)) :
    Subsingleton (HomotopyGroup (Fin j) ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) x) := by
  have hk1 : k - 1 + 1 = k := by omega
  have e : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) ≃ₜ Work.Stems.sphere (k - 1) :=
    hk1 ▸ Homeomorph.refl _
  exact subsingleton_homotopyGroup_of_homeomorph e rfl j
    (Work.Stems.sphereConnectivity (k - 1) j hj (e x))

theorem subsingleton_prodAmb (k : ℕ) (X : Type*) [TopologicalSpace X] [ContractibleSpace X]
    {j : ℕ} (hj : j + 1 < k)
    (z : X × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) × ↥(Set.Ioo (1 : ℝ) 2)) :
    Subsingleton (HomotopyGroup (Fin j)
      (X × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) × ↥(Set.Ioo (1 : ℝ) 2)) z) := by
  haveI : ContractibleSpace ↥(Set.Ioo (1 : ℝ) 2) :=
    (convex_Ioo 1 2).contractibleSpace ⟨3 / 2, by norm_num⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have hk2 : 2 ≤ k := by omega
    haveI : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) := by
      have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin k)) := by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        exact_mod_cast (by omega : 1 < k)
      exact (isPathConnected_iff_pathConnectedSpace).mp (isPathConnected_sphere hrank 0 (by norm_num))
    exact subsingleton_piZero_of_pathConnected z
  · haveI : Nonempty (Fin j) := ⟨⟨0, hpos⟩⟩
    obtain ⟨e2⟩ := Work.Stems.homotopyGroup_prod (N := Fin j) z.2.1 z.2.2
    obtain ⟨e1⟩ := Work.Stems.homotopyGroup_prod (N := Fin j) z.1 z.2
    have hS : Subsingleton
        (HomotopyGroup (Fin j) ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) z.2.1) :=
      subsingleton_sphere_amb k (by omega) z.2.1
    have hX : Subsingleton (HomotopyGroup (Fin j) X z.1) :=
      Work.Stems.subsingleton_of_contractible z.1
    have hI : Subsingleton (HomotopyGroup (Fin j) ↥(Set.Ioo (1 : ℝ) 2) z.2.2) :=
      Work.Stems.subsingleton_of_contractible z.2.2
    haveI h2 : Subsingleton (HomotopyGroup (Fin j)
        (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) × ↥(Set.Ioo (1 : ℝ) 2))
        (z.2.1, z.2.2)) := ⟨fun a b => e2.injective (Subsingleton.elim _ _)⟩
    haveI h1 : Subsingleton (HomotopyGroup (Fin j)
        (X × (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) × ↥(Set.Ioo (1 : ℝ) 2)))
        (z.1, z.2)) := ⟨fun a b => e1.injective (Subsingleton.elim _ _)⟩
    simpa only [Prod.mk.eta] using h1

theorem subsingleton_annOver (k m : ℕ) (S₀ : ChartIdx k m) (U : Set (OG k m))
    (hUsub : U ⊆ (tautologicalBundle k m).baseSet S₀) [ContractibleSpace ↥U]
    {j : ℕ} (hj : j + 1 < k) (y : ↥(Torsion.annOver k m U)) :
    Subsingleton (HomotopyGroup (Fin j) ↥(Torsion.annOver k m U) y) :=
  subsingleton_homotopyGroup_of_homeomorph (Torsion.annOverHomeomorph S₀ hUsub) rfl j
    (subsingleton_prodAmb k ↥U hj _)

theorem subsingleton_shellOver (k m : ℕ) (S₀ : ChartIdx k m) (U : Set (OG k m))
    (hUsub : U ⊆ (tautologicalBundle k m).baseSet S₀) [ContractibleSpace ↥U]
    {j : ℕ} (hj : j + 1 < k) (x : ↥(shellOver k m U)) :
    Subsingleton (HomotopyGroup (Fin j) ↥(shellOver k m U) x) :=
  subsingleton_shellOver_of_annOver k m U (fun y => subsingleton_annOver k m S₀ U hUsub hj y) x



/-! ## The two-set Mayer–Vietoris theorem without the unused degree hypothesis -/

/-- **The two-set connectivity theorem.**  If `X = U ∪ V` with `U, V` open, `U ∩ V` nonempty, the
homotopy groups `πᵢ` of `U` and `V` trivial for `i < k` and those of `U ∩ V` trivial for
`i + 1 < k`, then `πⱼ(X)` is trivial for `j < k` at every base point.

This is `Work.ThomBordism.Grassmann.twoSetConnected` without its (unused) hypothesis `2 ≤ k`; the
proof is the same, so the statement is available in the boundary cases `k ≤ 1` as well. -/
theorem twoSetConnected' {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (hne : (U ∩ V).Nonempty) (k : ℕ)
    (hUk : ∀ j, j < k → ∀ x : ↥U, Subsingleton (HomotopyGroup (Fin j) ↥U x))
    (hVk : ∀ j, j < k → ∀ x : ↥V, Subsingleton (HomotopyGroup (Fin j) ↥V x))
    (hUVk : ∀ j, j + 1 < k → ∀ x : ↥(U ∩ V), Subsingleton (HomotopyGroup (Fin j) ↥(U ∩ V) x)) :
    ∀ j, j < k → ∀ x : X, Subsingleton (HomotopyGroup (Fin j) X x) := by
  intro j hj x
  have hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d :=
    compress_trace_of_subsingleton (U := U) (V := V) (j := j)
      (fun d hd v => hVk d (by omega) v)
      (fun d hd w => hUVk d (by omega) w) hne
  have hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d :=
    compress_trace_of_subsingleton (U := V) (V := U) (j := j)
      (fun d hd u => hUk d (by omega) u)
      (fun d hd w => by
        have hbase : interSwapHomeo w = (⟨w.1, ⟨w.2.2, w.2.1⟩⟩ : ↥(U ∩ V)) := rfl
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · subst h0
          exact subsingleton_piZero_of_homeomorph interSwapHomeo hbase
            (hUVk 0 (by omega) ⟨w.1, ⟨w.2.2, w.2.1⟩⟩)
        · haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
          exact subsingleton_of_homeomorph interSwapHomeo hbase (Fin d)
            (hUVk d (by omega) ⟨w.1, ⟨w.2.2, w.2.1⟩⟩))
      (hne.elim fun z hz => ⟨z, ⟨hz.2, hz.1⟩⟩)
  have hXU : Compress X U j := compressRel_twoSet hU hV hcov j hVc hUc
  have hXV : Compress X V j := compressRel_twoSet hV hU (by rw [Set.union_comm]; exact hcov) j hUc hVc
  have hxu : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcov]; trivial
    exact this
  rcases hxu with hx | hx
  · exact Compress.toSubsingleton (U := U) hXU hx (hUk j hj ⟨x, hx⟩)
  · exact Compress.toSubsingleton (U := V) hXV hx (hVk j hj ⟨x, hx⟩)


/-! ## The main theorem -/

/-- **The Thom-space piece over a contractible chart piece is `(k-1)`-connected.**

For `U` open, `U ⊆ baseSet S₀` and `U` contractible (hence nonempty), the piece
`Z = pieceCover k m U = far 1 ∪ π⁻¹ U ⊆ Th γ = OnePoint (TotalSpace γ)`, with the subspace
topology, has `π_j(Z) = 0` for every `j < k` and every base point.

Recommended route (all ingredients proved in the workspace):

* `Z = far 1 ∪ π⁻¹ U` is a union of the two open subsets `A := far k m 1` (note `far 1 ⊆ Z`) and
  `B := π⁻¹ U`, so `twoSetConnected` (`Work.ThomBordism.Grassmann.twoSetConnected`) applies to the
  subspace `↥Z` with the traces of `A` and `B`;
* the trace of `A` in `Z` is `↥(far k m 1)`, which is contractible
  (`Work.ThomBordism.Grassmann.Torsion.contractibleFar`);
* the trace of `B` is `↥((tautologicalBundle k m).proj ⁻¹' U)`, homeomorphic to `↥U × ℝ^k` by the
  chart trivialisation `Work.Thom.ChartOrientation.chartHomeo` (with `hUsub`), hence contractible;
* the trace of `A ∩ B` is `{p : proj ⁻¹' U | 1 < fibN p}`; via `chartHomeo` and
  `Work.ThomBordism.Grassmann.exists_homeo_nuDisc` it is homotopy equivalent to `↥U × S^{k-1}`,
  whose `π_j` vanish for `j ≤ k - 2` by `Work.Stems.sphereConnectivity` (`twoSetConnected` needs
  this only for `j + 1 < k`); the relevant group decompositions are
  `Work.Stems.homotopyGroup_prod` / `Work.Stems.mulEquiv_of_homotopyEquiv`.

**Do not** try the stronger statement for arbitrary open `U ⊆ baseSet S₀` without contractibility:
it is false (for `U ≅ ℝ^{km} ∖ {0}` and `j ≥ 1` the piece is not `j`-connected), and the file
`pieceOverChartConnected.lean` / `pieceHomotopyCubed.lean` in this directory contain that statement
with an invalid proof — do not import them. -/
theorem pieceConnectedOfContractible (k m : ℕ) (S₀ : ChartIdx k m) (U : Set (OG k m))
    (hUopen : IsOpen U) (hUsub : U ⊆ (tautologicalBundle k m).baseSet S₀)
    (hUne : Nonempty ↥U) (hUc : ContractibleSpace ↥U) :
    ∀ j : ℕ, j < k → ∀ x : ↥(pieceCover k m U),
      Subsingleton (HomotopyGroup (Fin j) ↥(pieceCover k m U) x) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · intro j hj
    exact absurd hj (by omega)
  haveI := hUc
  -- the two open traces of `far 1` and of `π⁻¹ U` inside the piece
  refine twoSetConnected' (X := ↥(pieceCover k m U))
    (U := {z : ↥(pieceCover k m U) | (z : Torsion.TP k m) ∈ Torsion.far k m 1})
    (V := {z : ↥(pieceCover k m U) |
      (z : Torsion.TP k m) ∈ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)})
    ?_ ?_ ?_ ?_ k ?_ ?_ ?_
  · exact (Torsion.isOpen_far_one k m).preimage continuous_subtype_val
  · refine (OnePoint.isOpenEmbedding_coe.isOpenMap _
      ((Work.TangentClasses.RealBundle.continuous_proj _).isOpen_preimage _ hUopen)).preimage
      continuous_subtype_val
  · refine Set.eq_univ_of_forall fun z => ?_
    show (z : Torsion.TP k m) ∈ Torsion.far k m 1 ∪
      OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)
    exact z.2
  · -- a point of the total space over `U` with `fibN > 1`
    obtain ⟨u⟩ := hUne
    have hnorm : ‖(EuclideanSpace.single ⟨0, hkpos⟩ (1 : ℝ) : Amb k)‖ = 1 := by
      rw [PiLp.norm_single]; norm_num
    have hvne : (EuclideanSpace.single ⟨0, hkpos⟩ (1 : ℝ) : Amb k) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact one_ne_zero hnorm.symm
    set v : Amb k := EuclideanSpace.single ⟨0, hkpos⟩ (1 : ℝ) with hv
    have hpos : 0 < Torsion.fibN k m (Torsion.chartPt S₀ ⟨u.1, hUsub u.2⟩ v) :=
      Torsion.chartPt_fibN_pos S₀ ⟨u.1, hUsub u.2⟩ hvne
    set p : Torsion.TM k m :=
      Torsion.fibScale (2 / Torsion.fibN k m (Torsion.chartPt S₀ ⟨u.1, hUsub u.2⟩ v))
        (Torsion.chartPt S₀ ⟨u.1, hUsub u.2⟩ v) with hp
    have hc : 0 ≤ 2 / Torsion.fibN k m (Torsion.chartPt S₀ ⟨u.1, hUsub u.2⟩ v) := by positivity
    have hfib : Torsion.fibN k m p = 2 := by
      rw [hp]
      rw [Torsion.fibN_fibScale hc]
      field_simp
    have hproj : p.1 ∈ U := by
      rw [hp]
      show u.1 ∈ U
      exact u.2
    refine ⟨⟨OnePoint.some p, some_mem_pieceCover k m hproj⟩, ?_, ?_⟩
    · exact (Torsion.some_mem_far_iff k m 1 p).mpr (by rw [hfib]; norm_num)
    · exact ⟨p, hproj, rfl⟩
  · -- the trace of `far 1` is contractible
    intro j hj x
    have hsub : Torsion.far k m 1 ⊆ pieceCover k m U := fun y hy => Or.inl hy
    haveI : ContractibleSpace ↥(Torsion.far k m 1) := Torsion.contractibleFar k m
    exact subsingleton_homotopyGroup_of_homeomorph (subSubHomeo hsub) rfl j
      (Work.Stems.subsingleton_of_contractible ((subSubHomeo hsub) x))
  · -- the trace of `π⁻¹ U` is homeomorphic to `↥U × ℝ^k`, hence contractible
    intro j hj x
    have hbaseSet : U ⊆ ((tautologicalBundle k m).localTriv S₀).baseSet := fun y hy => hUsub hy
    have hpre : OnePoint.some ⁻¹' (OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U))
        = (tautologicalBundle k m).proj ⁻¹' U :=
      Set.preimage_image_eq _ (Option.some_injective _)
    have hBr : OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U) ⊆
        Set.range (OnePoint.some : Torsion.TM k m → Torsion.TP k m) :=
      fun y hy => by rcases hy with ⟨p, -, rfl⟩; exact ⟨p, rfl⟩
    have hsubZ : OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U) ⊆ pieceCover k m U :=
      fun y hy => Or.inr hy
    let e : ↥{z : ↥(pieceCover k m U) |
          (z : Torsion.TP k m) ∈ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)}
        ≃ₜ (↥U × Amb k) :=
      (subSubHomeo hsubZ).trans
        (((OnePoint.isOpenEmbedding_coe.isEmbedding).homeomorphOfSubsetRange hBr).symm.trans
          ((Homeomorph.setCongr hpre).trans
            (((tautologicalBundle k m).localTriv S₀).preimageHomeomorph hbaseSet)))
    exact subsingleton_homotopyGroup_of_homeomorph e rfl j
      (Work.Stems.subsingleton_of_contractible (e x))
  · -- the trace of the intersection is the shell over `U`, which is covered by a delegated lemma
    intro j hj x
    have hshell : OnePoint.some ⁻¹' (Torsion.far k m 1 ∩
        OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)) = shellOver k m U := by
      ext p
      constructor
      · intro hp
        rw [Set.mem_preimage, Set.mem_inter_iff] at hp
        obtain ⟨h1, q, hq, hqp⟩ := hp
        rw [Torsion.some_mem_far_iff] at h1
        have hpq : q = p := Option.some.inj hqp
        rw [hpq] at hq
        exact ⟨h1, hq⟩
      · intro hp
        rw [Set.mem_preimage, Set.mem_inter_iff]
        exact ⟨(Torsion.some_mem_far_iff k m 1 p).mpr hp.1, ⟨p, hp.2, rfl⟩⟩
    have hsubZ : Torsion.far k m 1 ∩ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)
        ⊆ pieceCover k m U := fun y hy => Or.inl hy.1
    have hBr : Torsion.far k m 1 ∩ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U) ⊆
        Set.range (OnePoint.some : Torsion.TM k m → Torsion.TP k m) :=
      fun y hy => by rcases hy.2 with ⟨p, -, rfl⟩; exact ⟨p, rfl⟩
    let e : ↥({z : ↥(pieceCover k m U) | (z : Torsion.TP k m) ∈ Torsion.far k m 1} ∩
          {z : ↥(pieceCover k m U) |
            (z : Torsion.TP k m) ∈ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' U)})
        ≃ₜ ↥(shellOver k m U) :=
      (subSubHomeo hsubZ).trans
        (((OnePoint.isOpenEmbedding_coe.isEmbedding).homeomorphOfSubsetRange hBr).symm.trans
          (Homeomorph.setCongr hshell))
    exact subsingleton_homotopyGroup_of_homeomorph e rfl j
      (subsingleton_shellOver k m S₀ U hUsub hj (e x))

end

end Work.ThomBordism.Grassmann.GoodCover
