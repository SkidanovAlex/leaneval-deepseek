import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.TrigIndep` — exponential independence of the lattice modes

The analytic core of `Work.BoseBoxFock.modeFam_independent`: a finite complex combination
`Σ i, c i * e^{I⟪ω i, x⟫}` of exponentials at **distinct** real frequencies vanishing on a
ball is identically zero, hence all coefficients vanish.

* `expSum_eq_zero_of_eqOn_Ioo` — the one-dimensional case, by induction with the
  differential operator `D - iλ` (dividing out one frequency at a time).  This is the only
  place where the analysis enters; everything else is algebra.
* `expSum_eq_zero_of_eqOn_ball` — the multivariate case, by restricting to the line
  `x₀ + t • v` for a direction `v` on which the frequencies are separated
  (`Function.Injective fun i => ⟪ω i, v⟫`), which the caller supplies.

Both are stated for an arbitrary finite index type; the box application instantiates them
with the lattice labels `Lab N` and the momenta `kmomLab ℓ N`.
-/

open scoped Real BigOperators
open Filter

namespace Work.BoseBoxFock

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma hasDerivAt_expLin (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (μ * (u : ℂ))) (Complex.exp (μ * (t : ℂ)) * μ) t := by
  have h1 : HasDerivAt (fun u : ℝ => μ * (u : ℂ)) μ t := by
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using h2.const_mul μ
  exact (Complex.hasDerivAt_exp (μ * (t : ℂ))).comp t h1

/-- **One-dimensional exponential independence.** -/
lemma expSum_eq_zero_of_eqOn_Ioo {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (c : ι → ℂ)
    (hlam : ∀ i ∈ s, ∀ j ∈ s, lam i = lam j → i = j) {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Set.Ioo a b,
      ∑ i ∈ s, c i * Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  suffices H : ∀ (s : Finset ι) (lam : ι → ℝ) (c : ι → ℂ),
      (∀ i ∈ s, ∀ j ∈ s, lam i = lam j → i = j) →
      (∀ t ∈ Set.Ioo a b,
        ∑ i ∈ s, c i * Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) = 0) →
      ∀ i ∈ s, c i = 0 from H s lam c hlam h
  intro s
  refine Finset.induction_on s ?base ?step
  case base =>
    intro lam c _ _ i hi
    exact absurd hi (Finset.notMem_empty i)
  case step =>
    intro i₀ s' hi₀ ih lam c hlam h
    have hlam' : ∀ i ∈ s', ∀ j ∈ s', lam i - lam i₀ = lam j - lam i₀ → i = j := by
      intro i hi j hj hij
      exact hlam i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) (by linarith)
    have h' : ∀ t ∈ Set.Ioo a b,
        ∑ i ∈ s', (c i * (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) *
          Complex.exp (Complex.I * (((lam i - lam i₀ : ℝ) : ℂ) * (t : ℂ))) = 0 := by
      intro t ht
      set F : ℝ → ℂ := fun u =>
        ∑ i ∈ insert i₀ s', c i * Complex.exp (Complex.I * ((lam i : ℂ) * (u : ℂ))) with hF
      have hderiv : HasDerivAt F
          (∑ i ∈ insert i₀ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
            (Complex.I * (lam i : ℂ)))) t := by
        rw [hF]
        refine HasDerivAt.fun_sum (fun i _ => ?_)
        have hh := (hasDerivAt_expLin (Complex.I * (lam i : ℂ)) t).const_mul (c i)
        simpa [mul_assoc] using hh
      have hF0 : HasDerivAt F 0 t := by
        have hmem : F =ᶠ[nhds t] (fun _ : ℝ => (0 : ℂ)) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
          rw [hF]
          exact h u hu
        exact (hasDerivAt_const (x := t) (c := (0 : ℂ))).congr_of_eventuallyEq hmem
      have hD : (∑ i ∈ insert i₀ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
            (Complex.I * (lam i : ℂ)))) = 0 := hderiv.unique hF0
      have hE : (∑ i ∈ insert i₀ s',
            c i * Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ)))) = 0 := h t ht
      have hkey : ∑ i ∈ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
            (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) = 0 := by
        have hsplit : (∑ i ∈ insert i₀ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
              (Complex.I * (lam i : ℂ)))) -
            (Complex.I * (lam i₀ : ℂ)) * (∑ i ∈ insert i₀ s',
              c i * Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))))
            = ∑ i ∈ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
              (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hi₀]
          have h0 : c i₀ * (Complex.exp (Complex.I * ((lam i₀ : ℂ) * (t : ℂ))) *
              (Complex.I * (lam i₀ : ℂ))) - Complex.I * (lam i₀ : ℂ) *
              (c i₀ * Complex.exp (Complex.I * ((lam i₀ : ℂ) * (t : ℂ)))) = 0 := by ring
          rw [h0, zero_add]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          ring
        rw [← hsplit, hD, hE, mul_zero, sub_zero]
      have hrel : ∑ i ∈ s', (c i * (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) *
            Complex.exp (Complex.I * (((lam i - lam i₀ : ℝ) : ℂ) * (t : ℂ))) =
          Complex.exp (-(Complex.I * ((lam i₀ : ℂ) * (t : ℂ)))) *
            ∑ i ∈ s', c i * (Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) *
              (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hexp : Complex.exp (-(Complex.I * ((lam i₀ : ℂ) * (t : ℂ)))) *
            Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) =
            Complex.exp (Complex.I * (((lam i - lam i₀ : ℝ) : ℂ) * (t : ℂ))) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← hexp]
        ring
      rw [hrel, hkey, mul_zero]
    have hS' : ∀ i ∈ s', c i = 0 := by
      intro i hi
      have h1 := ih (fun i => lam i - lam i₀)
        (fun i => c i * (Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)))) hlam' h' i hi
      have hne : Complex.I * ((lam i : ℂ) - (lam i₀ : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr ?_)
        intro hci
        have h2 : i = i₀ := hlam i (Finset.mem_insert_of_mem hi) i₀
          (Finset.mem_insert_self i₀ s') (by exact_mod_cast hci)
        subst h2
        exact hi₀ hi
      exact (mul_eq_zero.mp h1).resolve_right hne
    have hc0 : c i₀ = 0 := by
      have ht : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
      have hmid := h ((a + b) / 2) ht
      rw [Finset.sum_insert hi₀] at hmid
      have hz : ∑ i ∈ s', c i * Complex.exp (Complex.I * ((lam i : ℂ) * (((a + b) / 2 : ℝ) : ℂ))) = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [hS' i hi, zero_mul])
      rw [hz, add_zero] at hmid
      exact (mul_eq_zero.mp hmid).resolve_right (Complex.exp_ne_zero _)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hc0
    · exact hS' i hi'

/-- **Exponential independence on a ball** (the multivariate form): if a finite sum of
exponentials with distinct frequencies vanishes on a ball, all coefficients vanish.  The
separating direction `v` is given by the caller (`expSum_eq_zero_of_eqOn_Ioo` is applied
along the line through the centre in the direction `v`). -/
lemma expSum_eq_zero_of_eqOn_ball {ι : Type*} [Fintype ι] (ω : ι → ℝ³) (v : ℝ³)
    (hv : Function.Injective fun i => inner ℝ (ω i) v) (c : ι → ℂ) {x₀ : ℝ³} {ε : ℝ}
    (hε : 0 < ε)
    (h : ∀ x, ‖x - x₀‖ < ε →
      ∑ i, c i * Complex.exp (Complex.I * ((inner ℝ (ω i) x : ℝ) : ℂ)) = 0) :
    ∀ i, c i = 0 := by
  classical
  set δ : ℝ := ε / (2 * (‖v‖ + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hvn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have key : ∀ t : ℝ, |t| < δ →
      ∑ i, (c i * Complex.exp (Complex.I * ((inner ℝ (ω i) x₀ : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (((inner ℝ (ω i) v : ℝ) : ℂ) * (t : ℂ))) = 0 := by
    intro t ht
    have hx : ‖(x₀ + t • v) - x₀‖ < ε := by
      have h1 : (x₀ + t • v) - x₀ = t • v := by abel
      rw [h1, norm_smul, Real.norm_eq_abs]
      have h2 : |t| * ‖v‖ ≤ |t| * (‖v‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
      have h3 : |t| * (‖v‖ + 1) < δ * (‖v‖ + 1) :=
        mul_lt_mul_of_pos_right ht (by linarith)
      have h4 : δ * (‖v‖ + 1) = ε / 2 := by
        rw [hδdef]; field_simp
      linarith
    have h0 := h (x₀ + t • v) hx
    have hterm : ∀ i, c i * Complex.exp (Complex.I * ((inner ℝ (ω i) (x₀ + t • v) : ℝ) : ℂ))
        = (c i * Complex.exp (Complex.I * ((inner ℝ (ω i) x₀ : ℝ) : ℂ))) *
          Complex.exp (Complex.I * (((inner ℝ (ω i) v : ℝ) : ℂ) * (t : ℂ))) := by
      intro i
      have hin : inner ℝ (ω i) (x₀ + t • v) = inner ℝ (ω i) x₀ + inner ℝ (ω i) v * t := by
        rw [inner_add_right, real_inner_smul_right, mul_comm]
      have hexp : Complex.exp (Complex.I * ((inner ℝ (ω i) x₀ + inner ℝ (ω i) v * t : ℝ) : ℂ))
          = Complex.exp (Complex.I * ((inner ℝ (ω i) x₀ : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (((inner ℝ (ω i) v : ℝ) : ℂ) * (t : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hin, hexp]
      ring
    convert h0 using 1
    exact (Finset.sum_congr rfl (fun i _ => hterm i)).symm
  have h1d := expSum_eq_zero_of_eqOn_Ioo (s := Finset.univ)
    (lam := fun i => inner ℝ (ω i) v)
    (c := fun i => c i * Complex.exp (Complex.I * ((inner ℝ (ω i) x₀ : ℝ) : ℂ)))
    (hlam := fun i _ j _ hij => hv hij) (a := -δ) (b := δ) (by linarith)
    (by
      intro t ht
      rw [Set.mem_Ioo] at ht
      simpa using key t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
  intro i
  exact (mul_eq_zero.mp (h1d i (Finset.mem_univ i))).resolve_right (Complex.exp_ne_zero _)

-- ================= helpers =================

/-- Splitting a finite sum at a point `a`. -/
lemma sum_split_at {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℂ) :
    ∑ k, f k = f a + ∑ k, (if k = a then 0 else f k) := by
  classical
  have h1 : ∀ k, f k = (if k = a then f k else 0) + (if k = a then 0 else f k) := by
    intro k; by_cases h : k = a <;> simp [h]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- `(if k = a then z else y k) * g k` splits off the `a`-term. -/
lemma sum_ite_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (z : ℂ) (y g : ι → ℂ) :
    ∑ k, (if k = a then z else y k) * g k = z * g a + ∑ k, (if k = a then 0 else y k * g k) := by
  classical
  have h1 : ∀ k, (if k = a then z else y k) * g k
      = (if k = a then z * g k else 0) + (if k = a then 0 else y k * g k) := by
    intro k; by_cases h : k = a <;> simp [h]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

end Work.BoseBoxFock
