import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.uniqueness_energy_ineq
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.flat.linEnergyZero
import Submission.Work.Diff.STE.flat.antisymN_bound
import Submission.Work.Diff.STE.flat.coeffProps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Set

namespace Work.Diff.STE.flat

open Work.Diff.STE Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-! ## The antisymmetric part of a matrix-valued function

Everything in this file is about `Asym u t x i j = u t x i j - u t x j i`.  The target theorem says
that for a solution `u` of the flat DeTurck Cauchy problem `∂ₜu = Φ (·, jet u)` whose data are
symmetric, the antisymmetric part vanishes, provided `Φ` maps symmetric jets to symmetric values
(`hsym`) and the values of `u` satisfy a uniform quadratic-form lower bound (`hell`).

The proof follows the classical route (and the route the reviewers of this lemma suggested): the
antisymmetric part `w` satisfies a *linear* parabolic equation with an elliptic principal part and
a residual that is bounded by the size of `w` and `∇w`; the `L²` energy of `w` therefore obeys a
Grönwall inequality, and since `w` starts at `0` it vanishes identically.
-/

/-- The antisymmetric part `u t x i j - u t x j i` of a matrix valued function. -/
def Asym (u : ℝ → Torus n) : ℝ → Torus n := fun t x i j => u t x i j - u t x j i

@[simp] lemma Asym_apply (u : ℝ → Torus n) (t : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    Asym u t x i j = u t x i j - u t x j i := rfl

/-- The antisymmetric part of a periodic function is periodic. -/
lemma Asym_periodic {u : ℝ → Torus n} {t : ℝ} (hu : Periodic1 (u t)) :
    Periodic1 (Asym u t) := by
  intro i x
  funext a b
  rw [Asym_apply, Asym_apply, congrFun (congrFun (hu i x) a) b, congrFun (congrFun (hu i x) b) a]

/-- The entries of the antisymmetric part of a jointly smooth function are jointly smooth. -/
lemma Asym_contDiffOn {u : ℝ → Torus n} {T : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => Asym u p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
  (contDiffOn_entry_of_contDiffOn hu i j).sub (contDiffOn_entry_of_contDiffOn hu j i)

/-! ## The principal part of the DeTurck operator, antisymmetrised -/

/-- The antisymmetrisation of the scalar principal part `secOpFlat A B` acts on the second jet
slot: it is `Σ_{cd} (reMat A)⁻¹_{cd} (B_{cd,ij} - B_{cd,ji})`. -/
lemma secOpFlat_asym (A : MatC n) (B : Fin n → Fin n → MatC n) (i j : Fin n) :
    secOpFlat A B i j - secOpFlat A B j i
      = ∑ c, ∑ d, (((reMat A)⁻¹) c d : ℂ) * (B c d i j - B c d j i) := by
  simp only [secOpFlat]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun d _ => by ring)

/-- Replacing the coefficient of a double sum by its symmetrisation does not change the sum,
provided the summed kernel is symmetric. -/
lemma sum_symm_coeff (F : Fin n → Fin n → ℂ) (hF : ∀ c d, F c d = F d c)
    (A : Fin n → Fin n → ℂ) :
    (∑ c, ∑ d, ((A c d + A d c) / 2) * F c d) = ∑ c, ∑ d, A c d * F c d := by
  have hS : (∑ c, ∑ d, A d c * F c d) = ∑ c, ∑ d, A c d * F c d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hF d c]
  have hL : (2 : ℂ) * (∑ c, ∑ d, ((A c d + A d c) / 2) * F c d)
      = (∑ c, ∑ d, A c d * F c d) + (∑ c, ∑ d, A c d * F c d) := by
    simp only [Finset.mul_sum]
    rw [show (∑ c : Fin n, ∑ d : Fin n, (2 : ℂ) * (((A c d + A d c) / 2) * F c d))
        = ∑ c, ∑ d, (A c d + A d c) * F c d from
      Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by ring))]
    rw [show (∑ c : Fin n, ∑ d : Fin n, (A c d + A d c) * F c d)
        = ∑ c : Fin n, ((∑ d, A c d * F c d) + (∑ d, A d c * F c d)) from by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [show (∑ d : Fin n, (A c d + A d c) * F c d)
          = ∑ d, (A c d * F c d + A d c * F c d) from
        Finset.sum_congr rfl (fun d _ => by ring)]
      exact Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib, hS]
  refine mul_left_cancel₀ (two_ne_zero (α := ℂ)) ?_
  rw [hL, two_mul]

/-! ## The spatial jets of the antisymmetric part -/

/-- The first jet of the antisymmetric part is the antisymmetrised first jet. -/
lemma pdM_Asym {u : ℝ → Torus n} {t : ℝ} (c : Fin n) (x : Fin n → ℝ)
    (h : ∀ i j, Differentiable ℝ (fun y => u t y i j)) :
    pdM c (Asym u t) x
      = fun i j => pdM c (u t) x i j - pdM c (u t) x j i := by
  funext i j
  have h1 : pdM c (Asym u t) x i j = pd c (fun y => u t y i j - u t y j i) x := rfl
  rw [h1, pd_sub_fun c (h i j) (h j i)]
  rfl

/-- The second jet of the antisymmetric part is the antisymmetrised second jet. -/
lemma pd_pd_Asym {u : ℝ → Torus n} {t : ℝ} (c d : Fin n) (x : Fin n → ℝ)
    (h : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => u t y i j)) (i j : Fin n) :
    pd c (pd d (fun y => Asym u t y i j)) x
      = pdM c (pdM d (u t)) x i j - pdM c (pdM d (u t)) x j i := by
  have h1 : (fun y => Asym u t y i j) = fun y => u t y i j - u t y j i := rfl
  rw [h1, pd_pd_sub_fun c d (h i j) (h j i)]
  rfl

/-! ## Joint smoothness of the jet of a jointly smooth solution -/

/-- The `x`-slice of `Φ (·, jet u)` is continuously differentiable up to the jet of `u`: if `u` is
jointly smooth on `Ico 0 T × univ` and `reMat (u t x)` is invertible, then `(t,x) ↦ Φ (x, jetM (u t) x)`
is continuous there.  (`private`: the module `flat/continuousOn_phi_jet.lean` declares the same
statement and is the copy used downstream.) -/
private lemma continuousOn_phi_jet {Φ : (Fin n → ℝ) × Jet n → MatC n} {T : ℝ} {u : ℝ → Torus n}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      Φ (p.2, (u p.1 p.2, (fun c => pdM c (u p.1) p.2), (fun c d => pdM c (pdM d (u p.1)) p.2))))
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  set S : Set (ℝ × (Fin n → ℝ)) := Set.Ico (0:ℝ) T ×ˢ Set.univ with hS
  have hv : ∀ i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j) S :=
    fun i j => (contDiffOn_entry_of_contDiffOn hu i j).continuousOn
  have h1 : ∀ c i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => pdM c (u p.1) p.2 i j) S :=
    fun c i j => (contDiffOn_pd_slice (F := fun t x => u t x i j)
      (contDiffOn_entry_of_contDiffOn hu i j) c).continuousOn
  have h2 : ∀ c d i j, ContinuousOn
      (fun p : ℝ × (Fin n → ℝ) => pdM c (pdM d (u p.1)) p.2 i j) S :=
    fun c d i j => (contDiffOn_pd_slice (F := fun t x => pdM d (u t) x i j)
      (contDiffOn_pd_slice (F := fun t x => u t x i j)
        (contDiffOn_entry_of_contDiffOn hu i j) d) c).continuousOn
  have hjet : ContinuousOn
      (fun p : ℝ × (Fin n → ℝ) =>
        (p.2, (u p.1 p.2, (fun c => pdM c (u p.1) p.2), (fun c d => pdM c (pdM d (u p.1)) p.2)))) S := by
    refine ContinuousOn.prodMk continuous_snd.continuousOn ?_
    refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_)
    · rw [continuousOn_pi]
      intro i
      rw [continuousOn_pi]
      exact hv i
    · rw [continuousOn_pi]
      intro c
      rw [continuousOn_pi]
      intro i
      rw [continuousOn_pi]
      exact h1 c i
    · rw [continuousOn_pi]
      intro c
      rw [continuousOn_pi]
      intro d
      rw [continuousOn_pi]
      intro i
      rw [continuousOn_pi]
      exact h2 c d i
  have hmaps : Set.MapsTo
      (fun p : ℝ × (Fin n → ℝ) =>
        (p.2, (u p.1 p.2, (fun c => pdM c (u p.1) p.2), (fun c d => pdM c (pdM d (u p.1)) p.2))))
      S (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) :=
    fun p hp => ⟨Set.mem_univ _, hdet p.1 hp.1 p.2⟩
  exact hΦ.continuousOn.comp hjet hmaps

/-! ## The right-hand sides involved in the linearised equation for `Asym u`

`AsymRHS Φ u` is the right-hand side of the equation satisfied by the antisymmetric part (the
antisymmetrisation of the DeTurck nonlinearity), `secGOf a u` its principal part for a coefficient
family `a`, and `RfOf N u` the residual coming from the lower order term `N`. -/

/-- The antisymmetrisation of the right-hand side `Φ (·, jet u)` of the DeTurck equation. -/
def AsymRHS (Φ : (Fin n → ℝ) × Jet n → MatC n) (u : ℝ → Torus n) :
    ℝ → (Fin n → ℝ) → MatC n :=
  fun t x i j => Φ (x, jetM (u t) x) i j - Φ (x, jetM (u t) x) j i

/-- The principal part of the linearised equation, with the symmetrised coefficient `a`. -/
def secGOf (a : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Torus n) :
    ℝ → (Fin n → ℝ) → MatC n :=
  fun t x i j => ∑ c, ∑ d, ((a t x c d : ℂ) * pd c (pd d (fun y => Asym u t y i j)) x)

/-- The residual of the linearised equation: the antisymmetrisation of the lower order term `N`
of the DeTurck nonlinearity, evaluated at the jet of `u`. -/
def RfOf (N : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n) (u : ℝ → Torus n) :
    ℝ → (Fin n → ℝ) → MatC n :=
  fun t x i j =>
    N (x, (u t x, fun c => pdM c (u t) x)) i j - N (x, (u t x, fun c => pdM c (u t) x)) j i

/-! ## The key identity: `AsymRHS = secGOf + RfOf` -/

/-- **The linearisation of the antisymmetric part.**  The antisymmetrisation of the DeTurck
nonlinearity at the jet of a solution is the `secOpFlat`-part with the *symmetrised* inverse metric
coefficient (the antisymmetric part of the coefficient contributes nothing, because the second
partials of a smooth function commute) plus the antisymmetrised lower order term `N`. -/
lemma asymRHS_eq_secGOf_add_RfOf {Φ : (Fin n → ℝ) × Jet n → MatC n} {u : ℝ → Torus n}
    {N : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n}
    {a : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {T : ℝ}
    (hNdec : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n)
      (B : Fin n → Fin n → MatC n),
      (reMat A).det ≠ 0 → Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L)))
    (hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0)
    (ha : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x (c d : Fin n),
      a t x c d = (((reMat (u t x))⁻¹) c d + ((reMat (u t x))⁻¹) d c) / 2)
    (hslice : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u t y i j)) :
    ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x i j,
      AsymRHS Φ u t x i j = secGOf a u t x i j + RfOf N u t x i j := by
  intro t ht x i j
  have hslice_t : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u t y i j) := hslice t ht
  have hdec : Φ (x, jetM (u t) x)
      = secOpFlat (u t x) (fun c d => pdM c (pdM d (u t)) x)
        + N (x, (u t x, fun c => pdM c (u t) x)) :=
    hNdec x (u t x) (fun c => pdM c (u t) x) (fun c d => pdM c (pdM d (u t)) x) (hdet t ht x)
  have hjet : jetM (u t) x
      = (u t x, (fun c => pdM c (u t) x), fun c d => pdM c (pdM d (u t)) x) := rfl
  have hB : ∀ c d : Fin n,
      pdM c (pdM d (u t)) x i j - pdM c (pdM d (u t)) x j i
        = pd c (pd d (fun y => Asym u t y i j)) x :=
    fun c d => (pd_pd_Asym c d x hslice_t i j).symm
  -- the kernel of the symmetrised coefficient sum, and its symmetry (Clairaut)
  set F : Fin n → Fin n → ℂ := fun c d => pd c (pd d (fun y => Asym u t y i j)) x with hFdef
  have hFval : ∀ c d : Fin n, F c d = pd c (pd d (fun y => Asym u t y i j)) x := fun c d => rfl
  have hFsym : ∀ c d, F c d = F d c := by
    intro c d
    rw [hFval c d, hFval d c]
    exact cm_pd_comm_at (((hslice_t i j).sub (hslice_t j i)).of_le (by simp)).contDiffAt c d
  -- the symmetrisation of the coefficient
  have hsymsum : (∑ c, ∑ d, (((((reMat (u t x))⁻¹) c d : ℝ) : ℂ)
        + ((((reMat (u t x))⁻¹) d c : ℝ) : ℂ)) / 2 * F c d)
      = ∑ c, ∑ d, ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ) * F c d :=
    sum_symm_coeff F hFsym (fun c d => ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ))
  have haeq : ∀ c d : Fin n,
      (((((reMat (u t x))⁻¹) c d : ℝ) : ℂ) + ((((reMat (u t x))⁻¹) d c : ℝ) : ℂ)) / 2
        = (a t x c d : ℂ) := by
    intro c d
    rw [ha t ht x c d]
    push_cast
    ring
  calc AsymRHS Φ u t x i j
      = (secOpFlat (u t x) (fun c d => pdM c (pdM d (u t)) x) i j
          - secOpFlat (u t x) (fun c d => pdM c (pdM d (u t)) x) j i) + RfOf N u t x i j := by
        simp only [AsymRHS, RfOf, hdec, Pi.add_apply]
        ring
    _ = (∑ c, ∑ d, ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ)
            * (pdM c (pdM d (u t)) x i j - pdM c (pdM d (u t)) x j i)) + RfOf N u t x i j := by
        rw [secOpFlat_asym]
    _ = (∑ c, ∑ d, ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ) * F c d) + RfOf N u t x i j := by
        rw [show (∑ c : Fin n, ∑ d : Fin n, ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ)
              * (pdM c (pdM d (u t)) x i j - pdM c (pdM d (u t)) x j i))
            = ∑ c, ∑ d, ((((reMat (u t x))⁻¹) c d : ℝ) : ℂ) * F c d from
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by
            rw [hB c d, hFval c d]))]
    _ = (∑ c, ∑ d, (a t x c d : ℂ) * F c d) + RfOf N u t x i j := by
        rw [← hsymsum]
        congr 1
        exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by rw [haeq c d]))
    _ = secGOf a u t x i j + RfOf N u t x i j := by
        rw [show secGOf a u t x i j = ∑ c, ∑ d, (a t x c d : ℂ) * F c d from by
          simp only [secGOf, hFval]]

/-! ## The `L¹`-type norms controlling the residual -/

/-- The `L¹`-norm of a matrix, as a sum of the norms of its entries. -/
def entrySum (A : MatC n) : ℝ := ∑ i, ∑ j, ‖A i j‖

@[simp] lemma entrySum_apply (A : MatC n) : entrySum A = ∑ i, ∑ j, ‖A i j‖ := rfl

lemma entrySum_nonneg (A : MatC n) : 0 ≤ entrySum A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))

lemma norm_le_entrySum (A : MatC n) : ‖A‖ ≤ entrySum A := norm_le_sum_norm_matC A

/-- The same for the first jet of a matrix-valued function. -/
def jetSum (u : Torus n) (x : Fin n → ℝ) : ℝ :=
  ∑ c, ∑ i, ∑ j, ‖pdM c u x i j‖

@[simp] lemma jetSum_apply (u : Torus n) (x : Fin n → ℝ) :
    jetSum u x = ∑ c, ∑ i, ∑ j, ‖pdM c u x i j‖ := rfl

/-! ## Continuity and differentiability of the antisymmetrised right-hand side -/

/-- The antisymmetrised right-hand side is jointly continuous on the strip. -/
lemma continuousOn_asymRHS {Φ : (Fin n → ℝ) × Jet n → MatC n} {T : ℝ} {u : ℝ → Torus n}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => AsymRHS Φ u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  have hjet : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Φ (p.2, jetM (u p.1) p.2))
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    (continuousOn_phi_jet hΦ hu hdet).congr (fun p _ => rfl)
  have hentry : ∀ i j, ContinuousOn
      (fun p : ℝ × (Fin n → ℝ) => Φ (p.2, jetM (u p.1) p.2) i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    intro i j
    have hg : Continuous (fun M : MatC n => M i j) := (continuous_apply j).comp (continuous_apply i)
    have h := hg.comp_continuousOn hjet
    convert h using 1
    funext p
    rfl
  refine fun p hp => ?_
  rw [continuousWithinAt_pi]
  intro i
  rw [continuousWithinAt_pi]
  intro j
  have h := ((hentry i j).sub (hentry j i)) p hp
  convert h using 1
  funext q
  rfl

/-- The antisymmetric part satisfies the linearised equation whose right-hand side is
`AsymRHS Φ u`. -/
lemma hasDerivWithinAt_asym {Φ : (Fin n → ℝ) × Jet n → MatC n} {T : ℝ} {u : ℝ → Torus n}
    (hu : SolvesOn Φ T u) :
    ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s : ℝ => Asym u s x) (AsymRHS Φ u t x) (Set.Ico (0:ℝ) T) t := by
  intro t ht x
  refine hasDerivWithinAt_pi.mpr (fun i => hasDerivWithinAt_pi.mpr (fun j => ?_))
  have h1 : HasDerivWithinAt (fun s : ℝ => u s x) (Φ (x, jetM (u t) x))
      (Set.Ico (0:ℝ) T) t := hu.2.2 t ht x
  have h2 := hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp h1 i) j
  have h3 := hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp h1 j) i
  have h4 := h2.sub h3
  convert h4 using 1
  · funext s
    rfl
  · rfl

/-! ## Bounds on the jet of a solution over a compact strip -/

/-- The entries of `u` and of its first jet are uniformly bounded on `[0,tstar]` (times the unit
cube). -/
lemma jet_entry_bound {u : ℝ → Torus n} {T tstar : ℝ} (htstarT : tstar < T)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Ico (0:ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
      (∀ i j, ‖u t x i j‖ ≤ M) ∧ (∀ c i j, ‖pdM c (u t) x i j‖ ≤ M) := by
  set S : Set (ℝ × (Fin n → ℝ)) := Set.Ico (0:ℝ) T ×ˢ Set.univ with hSdef
  set K : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc (0:ℝ) tstar ×ˢ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) with hKdef
  have hKcompact : IsCompact K :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : K ⊆ S := fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 htstarT⟩, Set.mem_univ _⟩
  have h1 : ∀ i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => ‖u p.1 p.2 i j‖) S :=
    fun i j => (contDiffOn_entry_of_contDiffOn hu i j).continuousOn.norm
  have h2 : ∀ c i j, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => ‖pdM c (u p.1) p.2 i j‖) S :=
    fun c i j => (contDiffOn_pd_slice (F := fun t x => u t x i j)
      (contDiffOn_entry_of_contDiffOn hu i j) c).continuousOn.norm
  have hcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      (∑ i, ∑ j, ‖u p.1 p.2 i j‖) + (∑ c, ∑ i, ∑ j, ‖pdM c (u p.1) p.2 i j‖)) S := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ => h1 i j))
    · exact continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun i _ =>
        continuousOn_finsetSum _ (fun j _ => h2 c i j)))
  obtain ⟨M0, hM0⟩ := hKcompact.exists_bound_of_continuousOn (hcont.mono hKsub)
  refine ⟨max M0 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  have hmem : (t, x) ∈ K := ⟨⟨ht.1, ht.2.le⟩, hx⟩
  have hb := hM0 (t, x) hmem
  rw [Real.norm_of_nonneg (by positivity)] at hb
  have hnn1 : 0 ≤ ∑ i, ∑ j, ‖u t x i j‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  have hnn2 : 0 ≤ ∑ c, ∑ i, ∑ j, ‖pdM c (u t) x i j‖ :=
    Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => norm_nonneg _)))
  refine ⟨fun i j => ?_, fun c i j => ?_⟩
  · have hle := norm_entry_le_sum_matC (u t x) i j
    linarith [hle, hnn2, hb, le_max_left M0 0]
  · have hle := norm_entry_le_sum_pdM (u t) x c i j
    linarith [hle, hnn1, hb, le_max_left M0 0]

/-! ## Symmetry of the lower order term at symmetric jets -/

/-- At a symmetric jet with nondegenerate value the lower order term `N` of the DeTurck
nonlinearity is symmetric; this is what the hypothesis `hsym` of the theorem gives. -/
lemma N_symm_of_symm_jet {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {N : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n}
    (hsym : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n)
        (B : Fin n → Fin n → MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i)
    (hNdec : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n)
      (B : Fin n → Fin n → MatC n),
      (reMat A).det ≠ 0 → Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L)))
    (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n) (hdet : (reMat A).det ≠ 0)
    (hA : ∀ i j, A i j = A j i) (hL : ∀ c i j, L c i j = L c j i) :
    ∀ i j, N (x, (A, L)) i j = N (x, (A, L)) j i := by
  intro i j
  have h0 := hsym x A L (fun _ _ => (0 : MatC n)) hA hL
    (fun c d i j => rfl) (fun c d => rfl) i j
  have hdec : Φ (x, (A, L, (fun _ _ => (0 : MatC n)))) = secOpFlat A (fun _ _ => 0)
      + N (x, (A, L)) := hNdec x A L (fun _ _ => (0 : MatC n)) hdet
  rw [hdec] at h0
  simpa only [secOpFlat, Pi.add_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add] using h0

theorem SolvesOn_symm_of_jet {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (hsym : ∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) (hlam : 0 < lam)
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u)
    (h0 : ∀ (x : Fin n → ℝ) (i j : Fin n), u 0 x i j = u 0 x j i)
    (hell : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u t x) i j * v i * v j) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : Fin n → ℝ) (i j : Fin n), u t x i j = u t x j i := by
  -- ## unpacking the DeTurck shape
  obtain ⟨hΦsm, N, hNsm, hNdec, _hNper⟩ := hshape
  -- ## nondegeneracy of the metric matrix, from the ellipticity hypothesis
  have hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0 :=
    fun t ht x => det_ne_zero_of_quadratic (B := reMat (u t x)) hlam (hell t ht x)
  -- ## smoothness of the spatial slices
  have hslice : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ i j,
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u t y i j) :=
    fun t ht i j => contDiff_slice_of_contDiffOn (F := fun s y => u s y i j)
      (contDiffOn_entry_of_contDiffOn hu.1 i j) ht
  -- ## the properties of the antisymmetric part
  have hwsmooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => Asym u p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => Asym_contDiffOn hu.1 i j
  have hwper : ∀ t ∈ Set.Ico (0:ℝ) T, Periodic1 (Asym u t) :=
    fun t ht => Asym_periodic (hu.2.1 t ht)
  have hw0 : ∀ x i j, Asym u 0 x i j = 0 := fun x i j => sub_eq_zero.mpr (h0 x i j)
  have hPcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => AsymRHS Φ u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := continuousOn_asymRHS hΦsm hu.1 hdet
  have hderiv := hasDerivWithinAt_asym hu
  -- ## symmetry of the lower order term at symmetric jets
  have hsymN : ∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n),
      (reMat A).det ≠ 0 → (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      ∀ i j, N (x, (A, L)) i j = N (x, (A, L)) j i :=
    fun x A L hd hA hL => N_symm_of_symm_jet hsym hNdec x A L hd hA hL
  -- ## reduction to a compact strip `[0,tstar]`
  intro t₀ ht₀
  set tstar : ℝ := (t₀ + T) / 2 with htstardef
  have htstarT : tstar < T := by rw [htstardef]; linarith [ht₀.2]
  have ht₀tstar : t₀ ∈ Set.Ico (0:ℝ) tstar := ⟨ht₀.1, by rw [htstardef]; linarith [ht₀.2]⟩
  -- ## the symmetric elliptic coefficient, and the bounds it satisfies
  obtain ⟨a, lam', K₁, hlam', hK₁, ha_entry, haper, hasym, haid, hell', hdK⟩ :=
    coeffProps hn htstarT u hu.1 hu.2.1 lam hlam hell
  -- ## bounds on the jet of `u` over the compact strip
  obtain ⟨M, hM, hMbound⟩ := jet_entry_bound htstarT hu.1
  -- ## the Hadamard bound for the residual
  obtain ⟨CR, hCR, hCRb⟩ := antisymN_bound hn N hNsm hsymN M lam hM hlam
  -- ## the residual of the linearised equation obeys the Lipschitz bound
  have hres : ∀ t ∈ Set.Ico (0:ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
      ‖AsymRHS Φ u t x - secGOf a u t x‖
        ≤ CR * ((∑ i, ∑ j, ‖Asym u t x i j‖)
            + (∑ c, ∑ i, ∑ j, ‖pdM c (Asym u t) x i j‖)) := by
    intro t ht x hx
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_trans ht.2 htstarT⟩
    have hkey := asymRHS_eq_secGOf_add_RfOf hNdec hdet haid hslice t htT x
    have hdiff : AsymRHS Φ u t x - secGOf a u t x = RfOf N u t x := by
      funext i j
      rw [Pi.sub_apply, Pi.sub_apply, hkey i j]
      ring
    rw [hdiff]
    have hb := hCRb x hx (u t x) (fun c => pdM c (u t) x)
      (fun i j => (hMbound t ht x hx).1 i j) (fun c i j => (hMbound t ht x hx).2 c i j)
      (fun ξ => hell t htT x ξ)
    have hsum1 : (∑ i, ∑ j, ‖u t x i j - u t x j i‖) = ∑ i, ∑ j, ‖Asym u t x i j‖ := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rfl
    have hsum2 : (∑ c, ∑ i, ∑ j, ‖pdM c (u t) x i j - pdM c (u t) x j i‖)
        = ∑ c, ∑ i, ∑ j, ‖pdM c (Asym u t) x i j‖ := by
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => ?_)))
      rw [pdM_Asym c x (fun i j => (hslice t htT i j).differentiable (by simp))]
    refine le_trans hb (mul_le_mul_of_nonneg_left (le_of_eq ?_) hCR)
    rw [hsum1, hsum2]
  -- ## the energy/Grönwall argument for the antisymmetric part
  have hfin := linEnergyZero hn htstarT a (Asym u) (AsymRHS Φ u)
    ha_entry haper hasym hwsmooth hwper hPcont hderiv hw0 lam' K₁ CR hlam' hK₁ hCR hell' hdK hres
  intro x i j
  exact sub_eq_zero.mp (hfin t₀ ht₀tstar x i j)

end

end Work.Diff.STE.flat
