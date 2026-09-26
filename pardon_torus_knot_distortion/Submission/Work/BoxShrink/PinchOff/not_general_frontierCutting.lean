import Mathlib
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.SurgeryInvariance.WindingSpan.meridianCurve
import Submission.Work.BoxShrink.PinchOff.fundamentalSquare_winding_zero

/-!
# The general "frontier cutting" dimension bound is false

The statement

  `X ⊆ F`,  `Z ⊆ X`,  `X ∩ closure Z ⊆ Z`,  `W (frontier of X in F) = ⊥`,  `W Z = ⊥`
  `⟹  finrank (W X) ≤ finrank (W (X \ Z)) + 1`

— the dimension bound of the pinch-off with the two hypotheses of Pardon's local model replaced by
the weakness of the frontier of `X` and of `Z` — is **false** for arbitrary subsets `X`, `Z` of the
carrier of a parametrised torus.

The counterexample is the *theta graph*: the union `X = M ∪ L` of the meridian circle `M` at
`θ = 0` and the longitude circle `L` at `φ = 0`, cut at their single intersection point
`Z = {ψ 0 0}`.

* `W X = ⊤`: `X` contains the meridian and the longitude loop, whose winding vectors `(0,1)` and
  `(1,0)` span `ℚ² = H₁(T²; ℚ)`.
* `W Z = ⊥`: `Z` is a single point, so every curve inside it is constant and has winding `0`.
* `X` is compact, hence closed, so the frontier set `{x ∈ F | x ∈ closure X ∧ x ∉ X}` is empty.
* `W (X \ Z) = ⊥`: this is the only place where the geometry is used.  A curve of `X ∖ Z` lies in
  `M ∪ L` and avoids the only point `M ∩ L`; the sets where it lies on `M`, respectively on `L`,
  are therefore disjoint closed subsets of `ℝ` covering `ℝ`, hence clopen, so one of them is `ℝ`.
  A curve of the meridian circle (minus any point) is contained in the image of an open fundamental
  square `(a, a+2π) × (b, b+2π)` of the parameter plane, and a curve inside such a square has
  vanishing winding vector (`fundamentalSquare_winding_zero`).

So `finrank (W X) = 2 > 0 + 1` and the bound fails.  The two arcs of `X ∖ Z` are contractible, but
the *loops* of `X` are formed by going along one arc and returning along the other, through the
cut point — the phenomenon that the open/closed hypothesis on the pieces of `Z` in Pardon's
setting is designed to exclude.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

namespace FrontierCuttingCe

variable (P : Work.CoreTopology.ParamTorus)

/-- The meridian circle `{θ = 0}` of the torus `F = P.carrier`. -/
def meridian : Set R3 := Set.range fun φ : ℝ => P.psi 0 φ

/-- The longitude circle `{φ = 0}` of the torus `F = P.carrier`. -/
def longitude : Set R3 := Set.range fun θ : ℝ => P.psi θ 0

/-- The point where the meridian and the longitude circle meet. -/
def junction : R3 := P.psi 0 0

/-- The theta graph `X = M ∪ L`. -/
def theta : Set R3 := meridian P ∪ longitude P

/-- The cutting set `Z = {junction}`. -/
def cut : Set R3 := {junction P}

lemma meridian_subset_carrier : meridian P ⊆ P.carrier := by
  rintro x ⟨φ, rfl⟩
  exact P.psi_mem_carrier 0 φ

lemma longitude_subset_carrier : longitude P ⊆ P.carrier := by
  rintro x ⟨θ, rfl⟩
  exact P.psi_mem_carrier θ 0

lemma theta_subset_carrier : theta P ⊆ P.carrier := by
  rintro x (h | h)
  · exact meridian_subset_carrier P h
  · exact longitude_subset_carrier P h

lemma junction_mem_meridian : junction P ∈ meridian P := ⟨0, rfl⟩

lemma junction_mem_longitude : junction P ∈ longitude P := ⟨0, rfl⟩

lemma cut_subset_theta : cut P ⊆ theta P := by
  intro x hx
  rw [cut, Set.mem_singleton_iff] at hx
  subst hx
  exact Or.inl (junction_mem_meridian P)

/-- The parametrisation is invariant under the period lattice. -/
lemma psi_add_lattice (x y : ℝ) (k l : ℤ) :
    P.psi (x + (k : ℝ) * (2 * Real.pi)) (y + (l : ℝ) * (2 * Real.pi)) = P.psi x y := by
  have hy : Function.Periodic (fun y : ℝ => P.psi (x + (k : ℝ) * (2 * Real.pi)) y)
      (2 * Real.pi) := fun y => P.per_right (x + (k : ℝ) * (2 * Real.pi)) y
  have hx : Function.Periodic (fun x : ℝ => P.psi x y) (2 * Real.pi) := fun x => P.per_left x y
  calc P.psi (x + (k : ℝ) * (2 * Real.pi)) (y + (l : ℝ) * (2 * Real.pi))
      = P.psi (x + (k : ℝ) * (2 * Real.pi)) y := (hy.int_mul l) y
    _ = P.psi x y := (hx.int_mul k) x

lemma meridian_periodic : Function.Periodic (fun φ : ℝ => P.psi 0 φ) (2 * Real.pi) :=
  fun φ => P.per_right 0 φ

lemma longitude_periodic : Function.Periodic (fun θ : ℝ => P.psi θ 0) (2 * Real.pi) :=
  fun θ => P.per_left θ 0

/-- Every real number differs from an element of `[0, c)` by an integer multiple of `c`. -/
lemma exists_int_sub_mem_Ico (x c : ℝ) (hc : 0 < c) :
    ∃ k : ℤ, x - (k : ℝ) * c ∈ Set.Ico 0 c := by
  refine ⟨⌊x / c⌋, ?_, ?_⟩
  · have h : ((⌊x / c⌋ : ℤ) : ℝ) ≤ x / c := Int.floor_le _
    have h2 : ((⌊x / c⌋ : ℤ) : ℝ) * c ≤ x := (le_div_iff₀ hc).mp h
    linarith
  · have h : x / c < ((⌊x / c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : x < (((⌊x / c⌋ : ℤ) : ℝ) + 1) * c := (div_lt_iff₀ hc).mp h
    linarith

/-- If `f` is `2π`-periodic and `θ` is not a period multiple of `f`, then `f` takes at `θ` the same
value as at a point of the open interval `(0, 2π)`. -/
lemma exists_mem_Ioo_of_periodic (f : ℝ → R3) (hf : Function.Periodic f (2 * Real.pi)) (θ : ℝ)
    (h : ∀ k : ℤ, θ ≠ (k : ℝ) * (2 * Real.pi)) :
    ∃ θ' : ℝ, θ' ∈ Set.Ioo 0 (2 * Real.pi) ∧ f θ' = f θ := by
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico θ (2 * Real.pi) (by positivity)
  have hkne : θ - (k : ℝ) * (2 * Real.pi) ≠ 0 := by
    intro hzero
    exact h k (by linarith)
  refine ⟨θ - (k : ℝ) * (2 * Real.pi), ⟨lt_of_le_of_ne hk.1 (Ne.symm hkne), hk.2⟩, ?_⟩
  have hper := (hf.int_mul k) (θ - (k : ℝ) * (2 * Real.pi))
  have harg : (θ - (k : ℝ) * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi) = θ := by ring
  rw [harg] at hper
  exact hper.symm

lemma mem_meridian_iff_Icc (x : R3) :
    x ∈ meridian P ↔ ∃ φ : ℝ, φ ∈ Set.Icc 0 (2 * Real.pi) ∧ P.psi 0 φ = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨k, hk1, hk2⟩ := Work.TorusCover.exists_int_sub_mem_Icc φ
    refine ⟨φ - (k : ℝ) * (2 * Real.pi), ⟨hk1, hk2⟩, ?_⟩
    have hper := (meridian_periodic P).int_mul k (φ - (k : ℝ) * (2 * Real.pi))
    have harg : (φ - (k : ℝ) * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi) = φ := by ring
    rw [harg] at hper
    exact hper.symm
  · rintro ⟨φ, -, hφ⟩
    exact ⟨φ, hφ⟩

lemma mem_longitude_iff_Icc (x : R3) :
    x ∈ longitude P ↔ ∃ θ : ℝ, θ ∈ Set.Icc 0 (2 * Real.pi) ∧ P.psi θ 0 = x := by
  constructor
  · rintro ⟨θ, rfl⟩
    obtain ⟨k, hk1, hk2⟩ := Work.TorusCover.exists_int_sub_mem_Icc θ
    refine ⟨θ - (k : ℝ) * (2 * Real.pi), ⟨hk1, hk2⟩, ?_⟩
    have hper := (longitude_periodic P).int_mul k (θ - (k : ℝ) * (2 * Real.pi))
    have harg : (θ - (k : ℝ) * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi) = θ := by ring
    rw [harg] at hper
    exact hper.symm
  · rintro ⟨θ, -, hθ⟩
    exact ⟨θ, hθ⟩

lemma meridian_isClosed : IsClosed (meridian P) := by
  have himg : meridian P = (fun φ : ℝ => P.psi 0 φ) '' Set.Icc 0 (2 * Real.pi) := by
    ext x
    exact mem_meridian_iff_Icc P x
  rw [himg]
  exact (isCompact_Icc.image (P.meridianLoop_cont 0)).isClosed

lemma longitude_isClosed : IsClosed (longitude P) := by
  have himg : longitude P = (fun θ : ℝ => P.psi θ 0) '' Set.Icc 0 (2 * Real.pi) := by
    ext x
    exact mem_longitude_iff_Icc P x
  rw [himg]
  exact (isCompact_Icc.image (P.longitudeLoop_cont 0)).isClosed

lemma theta_isClosed : IsClosed (theta P) := (meridian_isClosed P).union (longitude_isClosed P)

/-- The two circles meet only at the junction point. -/
lemma inter_meridian_longitude : meridian P ∩ longitude P = {junction P} := by
  ext x
  constructor
  · rintro ⟨⟨φ, hφ⟩, ⟨θ, hθ⟩⟩
    have heq : P.psi 0 φ = P.psi θ 0 := hφ.trans hθ.symm
    obtain ⟨⟨k, hk⟩, -⟩ := (P.psi_eq_iff 0 φ θ 0).mp heq
    rw [Set.mem_singleton_iff]
    subst hθ
    dsimp only
    have hθ' : θ = 0 + (-k : ℤ) * (2 * Real.pi) := by
      push_cast
      linarith
    have hpsi : P.psi θ 0 = P.psi 0 0 := by
      rw [hθ']
      simpa using psi_add_lattice P 0 0 (-k) 0
    rw [hpsi]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨junction_mem_meridian P, junction_mem_longitude P⟩

/-- A constant closed curve has vanishing winding vector. -/
lemma windingOf_eq_zero_of_forall_eq (γ : Work.CoreTopology.ClosedCurve P) (x : R3)
    (h : ∀ t : ℝ, γ t = x) : Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
  have hx : x ∈ P.carrier := by rw [← h 0]; exact γ.mem 0
  obtain ⟨a, b, hab⟩ := (P.mem_carrier_iff x).mp hx
  let L : Work.CoreTopology.LiftOf P γ :=
    { Θ := fun _ => a
      Φ := fun _ => b
      contΘ := continuous_const
      contΦ := continuous_const
      lifts := fun t => by rw [hab, h t] }
  rw [Work.SurgeryInvariance.windingOf_eq P γ L]
  have h1 : ((L.winding).1 : ℝ) * (2 * Real.pi) = 0 := by
    have hspec := L.winding_spec.1
    have hc : L.Θ (2 * Real.pi) = L.Θ 0 := rfl
    linarith [hspec, hc]
  have h2 : ((L.winding).2 : ℝ) * (2 * Real.pi) = 0 := by
    have hspec := L.winding_spec.2
    have hc : L.Φ (2 * Real.pi) = L.Φ 0 := rfl
    linarith [hspec, hc]
  have hw1 : (L.winding).1 = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact_mod_cast h'
    · exact absurd h' (ne_of_gt (by positivity))
  have hw2 : (L.winding).2 = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact_mod_cast h'
    · exact absurd h' (ne_of_gt (by positivity))
  exact Prod.ext hw1 hw2

/-- **Every closed curve of `X ∖ Z` has vanishing winding vector.**  The curve lies in
`M ∪ L` (so the set of parameters where it is on `M` is a closed set, and likewise for `L`); these
two closed sets cover `ℝ` and are disjoint because `M ∩ L = {junction}` and the curve avoids the
junction.  Hence one of them is all of `ℝ`: the curve lies in the meridian circle or in the
longitude circle.  It also avoids the junction, so it lies in the image of the open fundamental
square `(-π, π) × (0, 2π)`, respectively `(0, 2π) × (-π, π)`, and
`fundamentalSquare_winding_zero` applies. -/
lemma windingOf_eq_zero_of_mem_theta_diff_cut (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ theta P \ cut P) :
    Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
  have hDM : IsClosed {t : ℝ | γ t ∈ meridian P} := (meridian_isClosed P).preimage γ.cont
  have hDL : IsClosed {t : ℝ | γ t ∈ longitude P} := (longitude_isClosed P).preimage γ.cont
  have hcover : (Set.univ : Set ℝ) ⊆
      {t : ℝ | γ t ∈ meridian P} ∪ {t : ℝ | γ t ∈ longitude P} := by
    intro t _
    have ht : γ t ∈ theta P := (hγ t).1
    rw [theta] at ht
    exact ht
  have hdisj : Disjoint {t : ℝ | γ t ∈ meridian P} {t : ℝ | γ t ∈ longitude P} := by
    rw [Set.disjoint_left]
    intro t htM htL
    have hmem : γ t ∈ meridian P ∩ longitude P := ⟨htM, htL⟩
    rw [inter_meridian_longitude P, Set.mem_singleton_iff] at hmem
    exact (hγ t).2 (by rw [cut]; exact hmem)
  have hcompl : ({t : ℝ | γ t ∈ meridian P})ᶜ = {t : ℝ | γ t ∈ longitude P} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro ht
      rcases hcover (Set.mem_univ t) with h | h
      · exact absurd h ht
      · exact h
    · intro ht htM
      exact Set.disjoint_left.mp hdisj htM ht
  have hopen : IsOpen {t : ℝ | γ t ∈ meridian P} := by
    rw [← isClosed_compl_iff, hcompl]
    exact hDL
  have hclopen : {t : ℝ | γ t ∈ meridian P} = Set.univ ∨ {t : ℝ | γ t ∈ meridian P} = ∅ := by
    rcases IsPreconnected.subset_or_subset (s := Set.univ) hopen hDM.isOpen_compl
      disjoint_compl_right (by rw [Set.union_compl_self]) isPreconnected_univ with h | h
    · exact Or.inl (Set.eq_univ_of_univ_subset h)
    · exact Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun x hx => h (Set.mem_univ x) hx)
  have hne : ∀ t : ℝ, γ t ≠ junction P := fun t => (hγ t).2
  rcases hclopen with hM | hM
  · refine Work.BoxShrink.PinchOff.fundamentalSquare_winding_zero P (-Real.pi) 0 γ ?_
    intro t
    have ht : γ t ∈ meridian P := Set.eq_univ_iff_forall.mp hM t
    obtain ⟨φ, hφ⟩ := ht
    have hφne : ∀ k : ℤ, φ ≠ (k : ℝ) * (2 * Real.pi) := by
      intro k hk
      exact hne t (by rw [← hφ, hk]; simpa [junction] using (meridian_periodic P).int_mul k 0)
    obtain ⟨φ', hφ'mem, hφ'eq⟩ := exists_mem_Ioo_of_periodic _ (meridian_periodic P) φ hφne
    exact ⟨(0, φ'), by constructor <;> linarith [Real.pi_pos], by simpa using hφ'mem,
      hφ'eq.trans hφ⟩
  · refine Work.BoxShrink.PinchOff.fundamentalSquare_winding_zero P 0 (-Real.pi) γ ?_
    intro t
    have htnot : γ t ∉ meridian P := Set.eq_empty_iff_forall_notMem.mp hM t
    have ht : γ t ∈ longitude P := by
      rcases hcover (Set.mem_univ t) with h | h
      · exact absurd h htnot
      · exact h
    obtain ⟨θ, hθ⟩ := ht
    have hθne : ∀ k : ℤ, θ ≠ (k : ℝ) * (2 * Real.pi) := by
      intro k hk
      exact hne t (by rw [← hθ, hk]; simpa [junction] using (longitude_periodic P).int_mul k 0)
    obtain ⟨θ', hθ'mem, hθ'eq⟩ := exists_mem_Ioo_of_periodic _ (longitude_periodic P) θ hθne
    exact ⟨(θ', 0), by simpa using hθ'mem, by constructor <;> linarith [Real.pi_pos],
      hθ'eq.trans hθ⟩

lemma windingSpan_theta_diff_cut_eq_bot :
    Work.SurgeryInvariance.WindingSpan P (theta P \ cut P) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hmem⟩
  exact ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess)
    (windingOf_eq_zero_of_mem_theta_diff_cut P γ hmem)

lemma windingSpan_empty : Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, -, hmem⟩
  exact hmem 0

lemma windingSpan_cut_eq_bot : Work.SurgeryInvariance.WindingSpan P (cut P) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hmem⟩
  have h : ∀ t : ℝ, γ t = junction P := by
    intro t
    have ht := hmem t
    rw [cut, Set.mem_singleton_iff] at ht
    exact ht
  exact ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess)
    (windingOf_eq_zero_of_forall_eq P γ (junction P) h)

lemma windingSpan_frontier_eq_bot :
    Work.SurgeryInvariance.WindingSpan P
      {x ∈ P.carrier | x ∈ closure (theta P) ∧ x ∉ theta P} = ⊥ := by
  have hcl : closure (theta P) = theta P := (theta_isClosed P).closure_eq
  have hempty : {x ∈ P.carrier | x ∈ closure (theta P) ∧ x ∉ theta P} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨-, hxcl, hxnot⟩
    exact hxnot (hcl ▸ hxcl)
  rw [hempty, windingSpan_empty P]

lemma windingSpan_theta_eq_top : Work.SurgeryInvariance.WindingSpan P (theta P) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hL : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P (theta P) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.longitudeCurve P 0, fun t => ?_, ?_⟩
    · rw [theta]
      exact Or.inr ⟨t, rfl⟩
    · have h := (Work.SurgeryInvariance.windingOf_eq P (Work.CoreTopology.longitudeCurve P 0)
        (Work.CoreTopology.longitudeLift P 0)).trans
        (Work.CoreTopology.longitudeLift_winding P 0)
      rw [h]
  have hM : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P (theta P) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve P 0, fun t => ?_, ?_⟩
    · rw [theta]
      exact Or.inl ⟨t, rfl⟩
    · have h := (Work.SurgeryInvariance.windingOf_eq P (Work.CoreTopology.meridianCurve P 0)
        (Work.CoreTopology.meridianLift P 0)).trans
        (Work.CoreTopology.meridianLift_winding P 0)
      rw [h]
  have hv : v = v.1 • ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) +
      v.2 • ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) := by
    ext <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hM)

lemma finrank_theta :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (theta P)) = 2 := by
  rw [windingSpan_theta_eq_top P,
    LinearEquiv.finrank_eq (Submodule.topEquiv (R := ℚ) (M := ℚ × ℚ)),
    Module.finrank_prod, Module.finrank_self]

lemma finrank_theta_diff_cut :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (theta P \ cut P)) = 0 := by
  rw [windingSpan_theta_diff_cut_eq_bot P]
  exact Submodule.finrank_eq_zero.mpr rfl

/-- The counterexample: the theta graph cut at its junction point satisfies all five hypotheses of
the claimed general frontier-cutting bound but violates its conclusion. -/
lemma exists_counterexample (P : Work.CoreTopology.ParamTorus) :
    ∃ X Z : Set R3,
      X ⊆ P.carrier ∧ Z ⊆ X ∧ X ∩ closure Z ⊆ Z ∧
      Work.SurgeryInvariance.WindingSpan P {x ∈ P.carrier | x ∈ closure X ∧ x ∉ X} = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P Z = ⊥ ∧
      ¬ (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X \ Z)) + 1) := by
  refine ⟨theta P, cut P, theta_subset_carrier P, cut_subset_theta P, ?_,
    windingSpan_frontier_eq_bot P, windingSpan_cut_eq_bot P, ?_⟩
  · rw [cut, closure_singleton]
    exact Set.inter_subset_right
  · intro hle
    rw [finrank_theta P, finrank_theta_diff_cut P] at hle
    omega

end FrontierCuttingCe

namespace Work.BoxShrink.PinchOff

theorem not_general_frontierCutting :
    ¬ (∀ (P : Work.CoreTopology.ParamTorus) (X Z : Set LeanEval.KnotTheory.PardonDistortion.R3),
        X ⊆ P.carrier →
        Z ⊆ X →
        X ∩ closure Z ⊆ Z →
        Work.SurgeryInvariance.WindingSpan P
          {x ∈ P.carrier | x ∈ closure X ∧ x ∉ X} = ⊥ →
        Work.SurgeryInvariance.WindingSpan P Z = ⊥ →
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤
          Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X \ Z)) + 1) := by
  intro h
  obtain ⟨X, Z, h1, h2, h3, h4, h5, h6⟩ :=
    FrontierCuttingCe.exists_counterexample Work.CoreTopology.standard
  exact h6 (h Work.CoreTopology.standard X Z h1 h2 h3 h4 h5)

end Work.BoxShrink.PinchOff
