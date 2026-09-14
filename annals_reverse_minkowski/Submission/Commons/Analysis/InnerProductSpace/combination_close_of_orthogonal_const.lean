import Mathlib.MeasureTheory.Function.L2Space

namespace Commons.Analysis.InnerProductSpace

open MeasureTheory Real
open scoped Real

/-- Auxiliary: `MemLp` is closed under finite sums. -/
private lemma memLp_finset_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    MemLp (∑ i ∈ s, f i) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Auxiliary: almost-everywhere equality is respected by finite sums of functions. -/
private lemma eventuallyEq_sum_fun {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    {s : Finset ι} {f g : ι → α → ℝ} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᵐ[μ] (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => filter_upwards with x; simp
  | insert a s ha ih =>
      filter_upwards [h a (Finset.mem_insert_self a s),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with x hx hix
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hx, hix]

/-- If every `L²(μ)`-function orthogonal to a set `S` of `L²(μ)`-functions is a.e. constant,
then every mean-zero `L²(μ)` function is approximable by finite linear combinations of `S`. -/
theorem combination_close_of_orthogonal_const {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : Set (α → ℝ))
    (hS : ∀ s ∈ S, MemLp s 2 μ)
    (horth : ∀ g : α → ℝ, MemLp g 2 μ → (∀ s ∈ S, ∫ x, g x * s x ∂μ = 0) →
      ∃ c : ℝ, g =ᵐ[μ] fun _ => c)
    (h : α → ℝ) (hh : MemLp h 2 μ) (hmean : ∫ x, h x ∂μ = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (s : Fin n → α → ℝ),
      (∀ i, s i ∈ S) ∧ MemLp (fun x => h x - ∑ i, c i * s i x) 2 μ ∧
      ∫ x, (h x - ∑ i, c i * s i x) ^ 2 ∂μ ≤ ε := by
  classical
  let A : Set (Lp ℝ 2 μ) := {x | ∃ s : α → ℝ, ∃ hs : s ∈ S, (hS s hs).toLp s = x}
  let T : Submodule ℝ (Lp ℝ 2 μ) := Submodule.span ℝ A
  -- (1) `h` is orthogonal to `Tᗮ`
  have hmem : hh.toLp h ∈ Tᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    have hgs : ∀ s ∈ S, ∫ x, g x * s x ∂μ = 0 := by
      intro s hs
      have hgen : (hS s hs).toLp s ∈ T := Submodule.subset_span ⟨s, hs, rfl⟩
      have hzero : inner ℝ ((hS s hs).toLp s) g = 0 :=
        (Submodule.mem_orthogonal T g).mp hg _ hgen
      rw [MeasureTheory.L2.inner_def] at hzero
      simp only [Real.inner_apply] at hzero
      have h1 : (fun a => ((hS s hs).toLp s) a * g a) =ᵐ[μ] (fun a => s a * g a) :=
        (hS s hs).coeFn_toLp.mul (ae_eq_refl g)
      have h2 : (fun a => s a * g a) =ᵐ[μ] (fun a => g a * s a) := by
        filter_upwards with a
        exact mul_comm _ _
      have heq : ∫ a, ((hS s hs).toLp s) a * g a ∂μ = ∫ a, g a * s a ∂μ := by
        rw [integral_congr_ae h1, integral_congr_ae h2]
      rw [heq] at hzero
      exact hzero
    obtain ⟨c, hc⟩ := horth (⇑g) (Lp.memLp g) hgs
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    have hae : (fun a => g a * (hh.toLp h) a) =ᵐ[μ] (fun a => c * h a) := by
      filter_upwards [hc, hh.coeFn_toLp] with a h1 h2
      rw [h1, h2]
    rw [integral_congr_ae hae, integral_const_mul, hmean, mul_zero]
  -- (2) hence `h` lies in the closure of the span of `S`
  have hcl : hh.toLp h ∈ closure (T : Set (Lp ℝ 2 μ)) := by
    have h1 := hmem
    rw [Submodule.orthogonal_orthogonal_eq_closure] at h1
    exact h1
  -- (3) approximate by an element of the span
  obtain ⟨y, hyT, hydist⟩ := Metric.mem_closure_iff.mp hcl (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  -- (4) extract a finite linear combination
  obtain ⟨n, cf, gfun, hgsum⟩ :=
    (Submodule.mem_span_set' (R := ℝ) (s := A)).mp hyT
  have hg2 : ∀ i, ∃ (s : α → ℝ) (hs : s ∈ S), (hS s hs).toLp s = (gfun i : Lp ℝ 2 μ) :=
    fun i => (gfun i).2
  choose sb hsb hLeq using hg2
  -- the corresponding real-valued combination
  let combfn : α → ℝ := fun x => ∑ i, cf i * sb i x
  have hcomb : MemLp combfn 2 μ := by
    have heqfun : combfn = ∑ i : Fin n, cf i • sb i := by
      funext x
      simp only [combfn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heqfun]
    exact memLp_finset_sum Finset.univ (fun i => cf i • sb i)
      (fun i _ => (hS (sb i) (hsb i)).const_smul (cf i))
  have hy_eq : y = hcomb.toLp combfn := by
    rw [← hgsum]
    apply MeasureTheory.Lp.ext
    have hR : (⇑(hcomb.toLp combfn) : α → ℝ) =ᵐ[μ] combfn := hcomb.coeFn_toLp
    have hL : (⇑(∑ i, cf i • (gfun i : Lp ℝ 2 μ)) : α → ℝ) =ᵐ[μ] combfn := by
      have hbase := MeasureTheory.Lp.coeFn_fun_finsetSum (p := 2) (μ := μ) (E := ℝ)
        Finset.univ (fun i => cf i • (gfun i : Lp ℝ 2 μ))
      refine hbase.trans ?_
      have h2 : (fun x => ∑ i ∈ Finset.univ, (cf i • (gfun i : Lp ℝ 2 μ)) x)
          =ᵐ[μ] (fun x => ∑ i ∈ Finset.univ, cf i * sb i x) :=
        eventuallyEq_sum_fun (fun i _ => by
          have hgi : (⇑(gfun i : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] sb i := by
            rw [← hLeq i]
            exact (hS (sb i) (hsb i)).coeFn_toLp
          have hsm : (⇑(cf i • (gfun i : Lp ℝ 2 μ)) : α → ℝ) =ᵐ[μ]
              (fun x => cf i * sb i x) := by
            filter_upwards [MeasureTheory.Lp.coeFn_smul (cf i) (gfun i : Lp ℝ 2 μ), hgi]
              with x hx1 hx2
            rw [hx1, Pi.smul_apply, smul_eq_mul, hx2]
          exact hsm)
      exact h2
    exact hL.trans hR.symm
  have hz : hh.toLp h - y = (hh.sub hcomb).toLp (h - combfn) := by
    rw [hy_eq, ← MemLp.toLp_sub hh hcomb]
  have hcoe : (hh.toLp h - y : Lp ℝ 2 μ) =ᵐ[μ] (h - combfn) := by
    rw [hz]
    exact (hh.sub hcomb).coeFn_toLp
  -- (5) the norm square is the desired integral
  have hnorm : ‖hh.toLp h - y‖ ^ 2 = ∫ x, (h x - combfn x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq (hh.toLp h - y)]
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx]
    simp only [Pi.sub_apply]
    ring
  have hdist2 : ‖hh.toLp h - y‖ ^ 2 < ε := by
    have h1 : ‖hh.toLp h - y‖ < Real.sqrt ε := by
      rw [← dist_eq_norm]; exact hydist
    have h2 := pow_lt_pow_left₀ h1 (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
    rwa [Real.sq_sqrt hε.le] at h2
  refine ⟨n, cf, sb, hsb, ?_, ?_⟩
  · exact hh.sub hcomb
  · rw [← hnorm]
    exact le_of_lt hdist2

end Commons.Analysis.InnerProductSpace