/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular commutator identity with radial derivatives

For `g` smooth on a neighbourhood of the closed quadrant and `i ≤ 3`, the identity

  `sin(2θ)·D_z^j D_θ^i(∂_θ g) = D_z^j D_θ^{i+1} g - Σ_{r=1}^{i} C(i,r) D_θ^r(sin 2·) · D_z^j D_θ^{i-r}(∂_θ g)`

holds on the neighbourhood `nbhU` of the closed quadrant.  Iterating it, and using the
`sin(2θ)`-divisibility `|D_θ^r(sin 2·)| ≤ A_r·sin(2θ)`, gives the bound

  `sin(2θ)·|D_z^j D_θ^i(∂_θ g)| ≤ C · Σ_{m=1}^{i+1} |D_z^j D_θ^m g|`.

This is the estimate which converts the "all derivatives on `g`" terms of the pairing into
weighted `L²`-slots (the paper's Case 1 commutator estimate).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.mixed_sin_bound
import Submission.Work.FTS.H2.T2SliceAux
import Submission.Work.Spaces.DzIterSmoothOn
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Congruence and linearity of the `D_z`-iterates on an open set -/

theorem Dz_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz u)) (Function.uncurry (Work.Spaces.Dz v)) V := by
  intro p hp
  show p.1 * Work.Spaces.pz u p.1 p.2 = p.1 * Work.Spaces.pz v p.1 p.2
  rw [Work.Spaces.pz_congr_of_isOpen hV h hp]

theorem DzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j u))
      (Function.uncurry (Work.Spaces.DzIter j v)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j v) p.1 p.2
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- `D_z` acts termwise on a finite sum with `θ`-dependent coefficients. -/
theorem Dz_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.Dz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 : DifferentiableAt ℝ ((Function.uncurry (F i)) ∘ (fun e : ℝ => (e, θ))) z :=
      h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  have h1 : Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ := by
    show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z = _
    have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
        = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
      funext z'; rw [Finset.sum_apply]
    rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
    exact Finset.sum_congr rfl fun i hi =>
      deriv_const_mul_field (c i θ)
  show z * Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * (z * Work.Spaces.pz (F i) z θ)
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by ring

/-- The `pz`-form of the same termwise identity. -/
theorem pz_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 : DifferentiableAt ℝ ((Function.uncurry (F i)) ∘ (fun e : ℝ => (e, θ))) z :=
      h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z
      = ∑ i ∈ s, c i θ * Work.Spaces.pz (F i) z θ
  have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
      = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
  exact Finset.sum_congr rfl fun i hi =>
    deriv_const_mul_field (c i θ)

theorem DzIter_sum_const_mul_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (F i)) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j (F i))) V :=
      fun i hi => Work.Spaces.DzIterSmoothOn hV (hF i hi) j
    have hstep := Dz_sum_const_mul_eqOn s c (fun i => Work.Spaces.DzIter j (F i)) hV hFs
    have hstep' := pz_sum_const_mul_eqOn s c (fun i => Work.Spaces.DzIter j (F i)) hV hFs
    intro p hp
    have hcongr : Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ))
          p.1 p.2
        = Work.Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (F i) z θ) p.1 p.2 :=
      Work.Spaces.pz_congr_of_isOpen hV ih hp
    have hstep'' := hstep' hp
    simp only [Function.uncurry] at hstep''
    show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) p.1 p.2
        = ∑ i ∈ s, c i p.2 * (p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (F i)) p.1 p.2)
    rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ))
            p.1 p.2
          = p.1 * Work.Spaces.pz
              (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) p.1 p.2 from rfl,
      hcongr, hstep'', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

/-! ## `D_θ` preserves `z`-independence -/

theorem Dth_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z θ, u z θ = u 0 θ) (z θ : ℝ) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth u 0 θ := by
  show Real.sin (2 * θ) * Work.Spaces.pth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u 0 θ
  congr 1
  show deriv (fun θ' => u z θ') θ = deriv (fun θ' => u 0 θ') θ
  congr 1
  funext θ'
  exact h z θ'

theorem DthIter_Sfun_zero (r : ℕ) : ∀ z θ : ℝ,
    Work.Spaces.DthIter r Sfun z θ = Work.Spaces.DthIter r Sfun 0 θ := by
  induction r with
  | zero => intro z θ; rfl
  | succ r ih =>
    intro z θ
    exact Dth_zindep (fun z' θ' => ih z' θ') z θ

/-! ## The Leibniz identity in `θ` on `nbhU`, with a `θ`-only coefficient -/

/-- `D_θ^{i+1} g` equals the Leibniz sum `∑_r C(i,r)·D_θ^r(sin 2·)·D_θ^{i-r}(∂_θ g)` on `nbhU`. -/
theorem dthIter_succ_eq_sum (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (i : ℕ) :
    Set.EqOn (Function.uncurry (fun z θ => Work.Spaces.DthIter (i + 1) g z θ))
      (Function.uncurry (fun z θ => ∑ r ∈ Finset.range (i + 1),
        ((i.choose r : ℝ) * Work.Spaces.DthIter r Sfun 0 θ)
          * Work.Spaces.DthIter (i - r) (Work.Spaces.pth g) z θ))
      Work.Spaces.nbhU := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  have hz1 : (-1 : ℝ) < z := hp.1
  have hθ1 : θ ∈ Set.Ioo (-1) (π / 2 + 1) := hp.2
  have hS : ContDiffOn ℝ ⊤ (fun θ' => Sfun z θ') (Set.Ioo (-1) (π / 2 + 1)) := by
    show ContDiffOn ℝ ⊤ (fun θ' => Real.sin (2 * θ')) _
    fun_prop
  have hpg : ContDiffOn ℝ ⊤ (fun θ' => Work.Spaces.pth g z θ') (Set.Ioo (-1) (π / 2 + 1)) := by
    refine contDiffOn_thslice_of_uncurry Work.Spaces.isOpen_nbhU
      (Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hg) isOpen_Ioo ?_
    intro θ' hθ'
    exact ⟨hz1, hθ'⟩
  have hkey := Work.Spaces.DthIter_mul i Sfun (Work.Spaces.pth g) z (Set.Ioo (-1) (π / 2 + 1))
    isOpen_Ioo hS hpg θ hθ1
  have hshift : Work.Spaces.DthIter i (fun z θ => Sfun z θ * Work.Spaces.pth g z θ)
      = Work.Spaces.DthIter (i + 1) g := by
    have h : Work.Spaces.DthIter i (Work.Spaces.DthIter 1 g)
        = Work.Spaces.DthIter (i + 1) g := Work.Spaces.DthIter_add_right i 1 g
    exact h
  rw [hshift] at hkey
  rw [hkey]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [DthIter_Sfun_zero r z θ]; ring

/-- The same identity, differentiated `j` times in `z`. -/
theorem mixed_succ_expansion (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (i j : ℕ)
    {z θ : ℝ} (hstrp : (z, θ) ∈ Work.Spaces.nbhU) :
    Work.Spaces.mixed j (i + 1) g z θ
      = Real.sin (2 * θ) * Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        + ∑ r ∈ Finset.range i,
            ((i.choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
              * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ := by
  have hF : ∀ r ∈ Finset.range (i + 1),
      ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter (i - r) (Work.Spaces.pth g)))
        Work.Spaces.nbhU := fun r _ =>
    contDiffOn_uncurry_DthIter Work.Spaces.isOpen_nbhU
      (Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hg) (i - r)
  have hsum := (DzIter_sum_const_mul_eqOn (Finset.range (i + 1))
      (fun r θ => (i.choose r : ℝ) * Work.Spaces.DthIter r Sfun 0 θ)
      (fun r => Work.Spaces.DthIter (i - r) (Work.Spaces.pth g)) Work.Spaces.isOpen_nbhU hF j) hstrp
  have hcongr := (DzIter_congr_of_isOpen Work.Spaces.isOpen_nbhU
    (dthIter_succ_eq_sum g hg i) j) hstrp
  have hsum' := hsum
  simp only [Function.uncurry] at hsum'
  have hcongr' := hcongr
  simp only [Function.uncurry] at hcongr'
  rw [show Work.Spaces.mixed j (i + 1) g z θ
        = Work.Spaces.DzIter j (fun z θ => Work.Spaces.DthIter (i + 1) g z θ) z θ from rfl]
  rw [hcongr', hsum', Finset.sum_range_succ', add_comm]
  rw [show Work.Spaces.DthIter 0 Sfun 0 θ = Real.sin (2 * θ) from rfl, Nat.sub_zero,
    Nat.choose_zero_right]
  simp only [Work.Spaces.mixed]
  ring


/-! ## The iterated commutator bound -/

/-- The constants of the iteration of `mixed_succ_expansion`:
`B n = 1 + ∑_{r<n} C(n,r+1)·A_{r+1}·B_{n-r-1}`. -/
def Bz : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 17
  | _ => 187

theorem Bz_rec (n : ℕ) (hn : n ≤ 3) :
    Bz n = 1 + ∑ r ∈ Finset.range n,
      ((n.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (n - (r + 1))) := by
  interval_cases n <;>
    simp [Bz, Asin, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero] <;>
    norm_num

theorem Bz_pos (n : ℕ) : 0 < Bz n := by
  rcases n with _ | _ | _ | _ <;> norm_num [Bz]

theorem Bz_nonneg (n : ℕ) : 0 ≤ Bz n := (Bz_pos n).le

/-- **The iterated commutator bound.**  For `i ≤ 3`, `sin(2θ)·|D_z^j D_θ^i(∂_θ g)|` is bounded
by a constant times the sum of the slots `|D_z^j D_θ^m g|`, `1 ≤ m ≤ i+1`. -/
theorem sigma_z_step (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (i : ℕ) (hi : i ≤ 3)
    (hIH : ∀ i' < i, ∀ j : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Spaces.nbhU →
      θ ∈ Set.Ioo 0 (π / 2) →
      Real.sin (2 * θ) * |Work.Spaces.mixed j i' (Work.Spaces.pth g) z θ|
        ≤ Bz i' * ∑ m ∈ Finset.Icc 1 (i' + 1), |Work.Spaces.mixed j m g z θ|)
    (j : ℕ) (z θ : ℝ) (hstrp : (z, θ) ∈ Work.Spaces.nbhU) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ|
      ≤ Bz i * ∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed j m g z θ| := by
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have h1 : Real.sin (2 * θ) * |Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ|
        = |Work.Spaces.mixed j 1 g z θ| := by
      have h2 : Real.sin (2 * θ) * Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ
          = Work.Spaces.mixed j 1 g z θ := by
        show Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth g) z θ = _
        exact sin_mul_dzIter_pth g j z θ
      calc Real.sin (2 * θ) * |Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ|
          = |Real.sin (2 * θ) * Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ| := by
            rw [abs_mul, abs_of_nonneg hS]
        _ = |Work.Spaces.mixed j 1 g z θ| := by rw [h2]
    rw [h1, Bz]
    have hT1 : (∑ m ∈ Finset.Icc 1 ((0:ℕ) + 1), |Work.Spaces.mixed j m g z θ|)
        = |Work.Spaces.mixed j 1 g z θ| := by
      rw [show Finset.Icc 1 ((0:ℕ) + 1) = {1} from rfl, Finset.sum_singleton]
    rw [hT1, one_mul]
  · set T : ℝ := ∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed j m g z θ| with hT
    have hTnn : 0 ≤ T := Finset.sum_nonneg fun m _ => abs_nonneg _
    have hexp := mixed_succ_expansion g hg i j hstrp
    have hrearr : Real.sin (2 * θ) * Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
        = Work.Spaces.mixed j (i + 1) g z θ
          - ∑ r ∈ Finset.range i,
              (((i:ℕ).choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
                * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ := by
      rw [hexp]; ring
    have hstep1 : Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ|
        ≤ |Work.Spaces.mixed j (i + 1) g z θ|
          + |∑ r ∈ Finset.range i,
              (((i:ℕ).choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
                * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ| := by
      have habs : Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ|
          = |Real.sin (2 * θ) * Work.Spaces.mixed j i (Work.Spaces.pth g) z θ| := by
        rw [abs_mul, abs_of_nonneg hS]
      rw [habs, hrearr]
      exact abs_sub_le_abs_add _ _
    refine le_trans hstep1 ?_
    -- bound the sum term by term
    have hterm : ∀ r ∈ Finset.range i,
        |(((i:ℕ).choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
            * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
          ≤ ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T := by
      intro r hr
      have hrle : r + 1 ≤ 3 := by
        simp only [Finset.mem_range] at hr; omega
      have hlt : i - (r + 1) < i := by omega
      have hAs := abs_DthIter_Sfun_le (r + 1) (by omega) 0 hθIθ
      have hCnn : (0 : ℝ) ≤ (i.choose (r + 1) : ℝ) := Nat.cast_nonneg _
      have hIHr := hIH (i - (r + 1)) hlt j z θ hstrp hθ
      have hsub : Finset.Icc 1 (i - (r + 1) + 1) ⊆ Finset.Icc 1 (i + 1) := by
        intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      have hTle : (∑ m ∈ Finset.Icc 1 (i - (r + 1) + 1), |Work.Spaces.mixed j m g z θ|)
          ≤ T := by
        rw [hT]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun m => |Work.Spaces.mixed j m g z θ|) hsub (fun m _ _ => abs_nonneg _)
      rw [abs_mul, abs_mul, abs_of_nonneg hCnn]
      have h1 : (i.choose (r + 1) : ℝ) * |Work.Spaces.DthIter (r + 1) Sfun 0 θ|
            * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
          ≤ (i.choose (r + 1) : ℝ) * (Asin (r + 1) * Real.sin (2 * θ))
            * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hAs hCnn
      refine le_trans h1 ?_
      have h2 : (i.choose (r + 1) : ℝ) * (Asin (r + 1) * Real.sin (2 * θ))
            * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
          = ((i.choose (r + 1) : ℝ) * Asin (r + 1))
            * (Real.sin (2 * θ) * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|) := by
        ring
      rw [h2]
      calc ((i.choose (r + 1) : ℝ) * Asin (r + 1))
            * (Real.sin (2 * θ) * |Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|)
          ≤ ((i.choose (r + 1) : ℝ) * Asin (r + 1)) * (Bz (i - (r + 1)) * T) :=
            mul_le_mul_of_nonneg_left
              (le_trans hIHr (mul_le_mul_of_nonneg_left hTle (Bz_nonneg _)))
              (mul_nonneg (Nat.cast_nonneg _) (Asin_pos _).le)
        _ = ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T := by ring
    have hsumabs : |∑ r ∈ Finset.range i,
          (((i:ℕ).choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
            * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
        ≤ ∑ r ∈ Finset.range i,
            ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
    have hw1 : |Work.Spaces.mixed j (i + 1) g z θ| ≤ T := by
      have hm : i + 1 ∈ Finset.Icc 1 (i + 1) := by simp
      rw [hT]
      exact Finset.single_le_sum (f := fun m => |Work.Spaces.mixed j m g z θ|)
        (fun m _ => abs_nonneg _) hm
    have hfin : T + ∑ r ∈ Finset.range i,
          ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T = Bz i * T := by
      rw [Bz_rec i hi, add_mul, one_mul,
        Finset.sum_mul]
    calc |Work.Spaces.mixed j (i + 1) g z θ|
          + |∑ r ∈ Finset.range i,
              (((i:ℕ).choose (r + 1) : ℝ) * Work.Spaces.DthIter (r + 1) Sfun 0 θ)
                * Work.Spaces.mixed j (i - (r + 1)) (Work.Spaces.pth g) z θ|
        ≤ T + ∑ r ∈ Finset.range i,
            ((i.choose (r + 1) : ℝ) * Asin (r + 1) * Bz (i - (r + 1))) * T :=
          add_le_add hw1 hsumabs
      _ = Bz i * T := hfin

theorem Bz_le (n : ℕ) : Bz n ≤ 187 := by
  rcases n with _ | _ | _ | _ <;> norm_num [Bz]

/-- The iterated commutator bound, assembled from `sigma_z_step` by induction on `i ≤ 3`. -/
theorem sigma_z_bound (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (i : ℕ) (hi : i ≤ 3)
    (j : ℕ) (z θ : ℝ) (hstrp : (z, θ) ∈ Work.Spaces.nbhU) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * |Work.Spaces.mixed j i (Work.Spaces.pth g) z θ|
      ≤ Bz i * ∑ m ∈ Finset.Icc 1 (i + 1), |Work.Spaces.mixed j m g z θ| := by
  revert j z θ
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j z θ hstrp hθ
    exact sigma_z_step g hg i hi (fun i' hi' => ih i' hi' (by omega)) j z θ hstrp hθ

end Work.FTS.H2
