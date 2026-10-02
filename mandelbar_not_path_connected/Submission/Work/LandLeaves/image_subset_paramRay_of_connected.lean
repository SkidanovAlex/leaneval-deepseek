import Mathlib
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.ELTop.All
import Submission.Work.ParamRays.Bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The image of a connected piece of a dynamical ray under a local inverse branch

Let `T_c z = z̄² + c` be the antiholomorphic quadratic family and
`φ` a dynamical Böttcher coordinate of `T_c` (`Work.ParamRays.IsDynBottcher c φ`), with
Böttcher data `hN : Work.EL.DynB c φ`.

Suppose `y` is a repelling periodic point of odd period `k` and `g` is a local right inverse of
the holomorphic second return map `τ = (T_c)^{2k}` on a ball `B(y, r')` around `y`
(`τ (g w) = w`).  If `C` is a **preconnected** set contained in a single dynamical ray
`Work.EL.paramRay hN θ` and inside `B(y, r')`, then the image `g '' C` lies in a single ray
`Work.EL.paramRay hN θ'`, and the angle transforms by the multiplier `4^k` of the angle-doubling
map: `4^k θ' = θ + m` for some integer `m`.

The proof does not use the repelling hypothesis: it only uses the Böttcher functional equation
`φ (τ z) = φ z ^ (4^k)` together with `τ (g w) = w`.  Reading it on the Böttcher coordinate,
we get `φ (g w)^(4^k) = φ w = t · e^{2πiθ}` on the ray; after dividing by a fixed value of
`e^{2πiθ/4^k}` the quotient `φ (g w) / (‖φ (g w)‖ e^{2πiθ/4^k})` is a `4^k`-th root of unity.  It
depends continuously on `w`, and the roots of unity are a countable (hence totally disconnected)
set, so by preconnectedness of `C` it is constant on `C`; that constant is `e^{2πi m/4^k}` and
gives `θ'`.
-/

open Classical Filter Set
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary dynamical facts about the filled Julia set -/

/-- The filled Julia set is forward invariant: `T_c` maps `K c` into itself. -/
private lemma mem_K_of_mem_K_Tantibar {c z : ℂ} (hz : z ∈ Work.EL.K c) :
    Tantibar c z ∈ Work.EL.K c := by
  have h1 := Work.ParamRays.BoundedOrbit.shift hz 1
  have h2 : Work.ParamRays.orbit c z 1 = Tantibar c z := by simp [Work.ParamRays.orbit]
  rw [h2] at h1
  exact h1

/-- The iterate of the filled Julia set stays in the filled Julia set. -/
private lemma iterate_mem_K {c z : ℂ} (hz : z ∈ Work.EL.K c) (n : ℕ) :
    (Tantibar c)^[n] z ∈ Work.EL.K c := by
  induction n with
  | zero => simpa using hz
  | succ m ih => rw [Function.iterate_succ_apply']; exact mem_K_of_mem_K_Tantibar ih

/-! ## Algebraic and analytic helper lemmas -/

/-- An `n`-th root of unity is `exp (2πi m / n)` for some integer `m`. -/
private lemma exists_int_exp_of_pow_eq_one {ρ : ℂ} {n : ℕ} (hn : n ≠ 0) (hρ : ρ ^ n = 1) :
    ∃ m : ℤ, ρ = Complex.exp (↑m * (2 * ↑Real.pi * Complex.I) / ↑n) := by
  have hρne : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hρ
    exact zero_ne_one hρ
  have hexp : Complex.exp (Complex.log ρ) = ρ := Complex.exp_log hρne
  have h1 : Complex.exp ((n : ℂ) * Complex.log ρ) = 1 := by
    rw [Complex.exp_nat_mul, hexp, hρ]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hm' : Complex.log ρ = ↑m * (2 * ↑Real.pi * Complex.I) / ↑n := by
    rw [eq_div_iff hnc, mul_comm]
    exact hm
  exact ⟨m, by rw [← hexp, hm']⟩

/-- `((4 ^ k : ℕ) : ℂ) = (((4 : ℝ) ^ k : ℝ) : ℂ)`. -/
private lemma cast_four_pow (k : ℕ) :
    ((4 ^ k : ℕ) : ℂ) = (((4 : ℝ) ^ k : ℝ) : ℂ) := by
  push_cast; ring

/-- `(((4 : ℝ) ^ k : ℝ) : ℂ) ≠ 0`. -/
private lemma cast_four_pow_ne (k : ℕ) : (((4 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by
  rw [← cast_four_pow k]
  exact_mod_cast pow_ne_zero k (by norm_num : (4 : ℕ) ≠ 0)

/-- The `4^k`-th power of `exp (2πiθ/4^k)` is `exp (2πiθ)`. -/
private lemma exp_div_pow (k : ℕ) (θ : ℝ) :
    (Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)) ^ (4 ^ k)
      = Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [cast_four_pow k]
  field_simp

/-- The product of `exp (2πiθ/4^k)` with the root of unity `exp (m · 2πi/4^k)` is
`exp (2πiθ')` with `θ' = (θ + m)/4^k`. -/
private lemma exp_mul_exp (k : ℕ) (θ : ℝ) (m : ℤ) :
    Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)
      * Complex.exp ((m : ℂ) * (2 * ↑Real.pi * Complex.I) / ((4 ^ k : ℕ) : ℂ))
      = Complex.exp (2 * ↑Real.pi * (((θ + (m : ℝ)) / ((4 : ℝ) ^ k)) : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  rw [cast_four_pow k]
  push_cast
  ring

/-- Writing `u^(4^k) = t · exp (2πiθ)` with `t > 0`, the normalized quotient
`u / (‖u‖ exp (2πiθ/4^k))` is a `4^k`-th root of unity. -/
private lemma div_norm_exp_pow_eq_one (k : ℕ) (θ : ℝ) (u : ℂ) (t : ℝ) (ht : 0 < t)
    (hu : u ^ (4 ^ k) = (t : ℂ) * Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I)) :
    ((u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I))
      / ‖u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)‖)
        ^ (4 ^ k) = 1 := by
  have hE := exp_div_pow k θ
  have hvn :
      (u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I))
        ^ (4 ^ k) = (t : ℂ) := by
    rw [div_pow, hE, hu]
    have hEne : Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have htn : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hnorm :
      ‖u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)‖
        ^ (4 ^ k) = t := by
    rw [← norm_pow, hvn]
    have h : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
    rw [h, abs_of_pos ht]
  rw [div_pow, hvn]
  rw [show (‖u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)‖ : ℂ)
      ^ (4 ^ k) = ((t : ℂ)) by rw [← Complex.ofReal_pow, hnorm]]
  exact div_self htn

/-- The level of `u / exp (2πiθ/4^k)`: its `4^k`-th power is `t`. -/
private lemma norm_div_exp_pow (k : ℕ) (θ : ℝ) (u : ℂ) (t : ℝ) (ht : 0 < t)
    (hu : u ^ (4 ^ k) = (t : ℂ) * Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I)) :
    ‖u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)‖ ^ (4 ^ k)
      = t := by
  have hE := exp_div_pow k θ
  have hvn :
      (u / Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I))
        ^ (4 ^ k) = (t : ℂ) := by
    rw [div_pow, hE, hu]
    have hEne : Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [← norm_pow, hvn]
  have h : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
  rw [h, abs_of_pos ht]

/-- If `E ≠ 0`, `u ≠ 0` and `E · (u/E)/‖u/E‖ = exp (2πiθ')`, then `u = rayPoint θ' ‖u/E‖`. -/
private lemma eq_rayPoint_of {θ' : ℝ} {u E : ℂ} (hEne : E ≠ 0) (hune : u ≠ 0)
    (hdir : E * ((u / E) / ‖u / E‖) = Complex.exp (2 * ↑Real.pi * (θ' : ℂ) * Complex.I)) :
    u = Work.Top.NakaneData.rayPoint θ' ‖u / E‖ := by
  have hwne : u / E ≠ 0 := div_ne_zero hune hEne
  have hnne : (‖u / E‖ : ℂ) ≠ 0 := by
    have h : ‖u / E‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
    exact_mod_cast h
  have h1 : u / E = ‖u / E‖ * ((u / E) / ‖u / E‖) := by field_simp
  calc u = E * (u / E) := by field_simp
    _ = E * (‖u / E‖ * ((u / E) / ‖u / E‖)) := by conv_lhs => rw [h1]
    _ = ‖u / E‖ * (E * ((u / E) / ‖u / E‖)) := by ring
    _ = ‖u / E‖ * Complex.exp (2 * ↑Real.pi * (θ' : ℂ) * Complex.I) := by rw [hdir]
    _ = Work.Top.NakaneData.rayPoint θ' ‖u / E‖ := by rw [Work.Top.NakaneData.rayPoint]

/-- The `n`-th roots of unity form a finite set. -/
private lemma finite_rootsOfUnity (n : ℕ) (hn : n ≠ 0) : Set.Finite {z : ℂ | z ^ n = 1} := by
  have hQ : (Polynomial.X ^ n - Polynomial.C (1 : ℂ) : Polynomial ℂ) ≠ 0 := by
    intro h
    have h2 : (0 : ℂ) ^ n - 1 = 0 := by
      simpa using congrArg (fun p => Polynomial.eval (0 : ℂ) p) h
    rw [zero_pow hn] at h2
    norm_num at h2
  refine (Polynomial.finite_setOfPred_isRoot hQ).subset ?_
  intro z hz
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hz ⊢
  exact sub_eq_zero.mpr hz

/-- A continuous function on a preconnected set whose values are `n`-th roots of unity is
constant. -/
private lemma preconnected_roots_subsingleton {n : ℕ} (hn : n ≠ 0) {C : Set ℂ}
    (hC : IsPreconnected C) (ζ : ℂ → ℂ) (hcont : ContinuousOn ζ C)
    (h1 : ∀ w ∈ C, ζ w ^ n = 1) : (ζ '' C).Subsingleton := by
  have hfin : Set.Finite {z : ℂ | z ^ n = 1} := finite_rootsOfUnity n hn
  have hpre : IsPreconnected (ζ '' C) := hC.image ζ hcont
  have hsub : ζ '' C ⊆ {z : ℂ | z ^ n = 1} := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := hz
    exact h1 w hw
  exact Set.Countable.isTotallyDisconnected hfin.countable (ζ '' C) hsub hpre

/-! ## The main theorem -/

theorem image_subset_paramRay_of_connected {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {r' : ℝ} (hr' : 0 < r') {g : ℂ → ℂ} (hgy : g y = y)
    (hcont : ContinuousOn g (Metric.ball y r'))
    (hright : ∀ w : ℂ, ‖w - y‖ ≤ r' → (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (g w) = w)
    {hN : Work.EL.DynB c φ} {θ : ℝ} {C : Set ℂ}
    (hC : C ⊆ (Work.EL.K c)ᶜ) (hCb : C ⊆ Metric.ball y r') (hconn : IsPreconnected C)
    (hray : C ⊆ Work.EL.paramRay hN θ) :
    ∃ θ' : ℝ, g '' C ⊆ Work.EL.paramRay hN θ' ∧ ∃ m : ℤ, (4 : ℝ) ^ k * θ' = θ + m := by
  classical
  rcases Set.eq_empty_or_nonempty C with hCempty | ⟨w₀, hw₀⟩
  · refine ⟨θ / (4 : ℝ) ^ k, ?_, 0, ?_⟩
    · rw [hCempty, Set.image_empty]
      exact Set.empty_subset _
    · rw [Int.cast_zero, add_zero]
      exact mul_div_cancel₀ θ (pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0))
  · have hn0 : (4 ^ k : ℕ) ≠ 0 := pow_ne_zero k (by norm_num)
    have hnN : ((4 ^ k : ℕ) : ℂ) = (((4 : ℝ) ^ k : ℝ) : ℂ) := cast_four_pow k
    have hNne : (((4 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := cast_four_pow_ne k
    -- the fixed value `E = exp (2πiθ/4^k)`
    set E : ℂ := Complex.exp (2 * ↑Real.pi * ((θ : ℂ) / (((4 : ℝ) ^ k : ℝ) : ℂ)) * Complex.I)
      with hEdef
    have hEne : E ≠ 0 := by rw [hEdef]; exact Complex.exp_ne_zero _
    -- the normalized root of unity at a point
    set ζ : ℂ → ℂ := fun w =>
      (Work.EL.dynPhi c φ (g w) / E) / ‖Work.EL.dynPhi c φ (g w) / E‖ with hζdef
    have hζfun : ζ = fun w =>
        (Work.EL.dynPhi c φ (g w) / E) / ‖Work.EL.dynPhi c φ (g w) / E‖ := by rw [hζdef]
    -- the ray data of a point of `C`
    have rayFacts : ∀ w ∈ C, w ∉ Work.EL.K c ∧ ∃ t : ℝ, 1 < t ∧
        Work.EL.dynPhi c φ w = Work.Top.NakaneData.rayPoint θ t := by
      intro w hw
      exact (Work.Top.NakaneData.mem_paramRay_iff hN).mp (hray hw)
    -- `g w` leaves the filled Julia set
    have gK : ∀ w ∈ C, g w ∉ Work.EL.K c := by
      intro w hw hgwK
      have hmem : (Tantibar c)^[2 * k] (g w) ∈ Work.EL.K c := iterate_mem_K hgwK (2 * k)
      have hdist : dist w y < r' := Metric.mem_ball.mp (hCb hw)
      have hnw : ‖w - y‖ ≤ r' := by rw [dist_eq_norm] at hdist; exact le_of_lt hdist
      rw [hright w hnw] at hmem
      exact (rayFacts w hw).1 hmem
    -- the Böttcher functional equation along the inverse branch
    have hdyn : ∀ w ∈ C, (Work.EL.dynPhi c φ (g w)) ^ (4 ^ k) = φ w := by
      intro w hw
      have hgwK := gK w hw
      have hesc : Work.ParamRays.Escaping c (g w) :=
        (Work.ParamRays.escaping_iff_not_bounded c (g w)).mpr hgwK
      have hfun := hφ.functional_iterate hesc k
      have hdist : dist w y < r' := Metric.mem_ball.mp (hCb hw)
      have hnw : ‖w - y‖ ≤ r' := by rw [dist_eq_norm] at hdist; exact le_of_lt hdist
      have hiter : Work.ParamRays.orbit c (g w) (2 * k) = w := by
        rw [Work.ParamRays.orbit]; exact hright w hnw
      rw [hiter] at hfun
      rw [Work.EL.dynPhi_of_notMem (φ := φ) hgwK]
      exact hfun.symm
    -- `ζ w` is always a `4^k`-th root of unity
    have hζ1 : ∀ w ∈ C, ζ w ^ (4 ^ k) = 1 := by
      intro w hw
      obtain ⟨t, ht, hwt⟩ := (rayFacts w hw).2
      have hphiw : φ w = Work.Top.NakaneData.rayPoint θ t := by
        rw [← Work.EL.dynPhi_of_notMem (φ := φ) (rayFacts w hw).1]; exact hwt
      have hu : (Work.EL.dynPhi c φ (g w)) ^ (4 ^ k)
          = (t : ℂ) * Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I) := by
        rw [hdyn w hw, hphiw, Work.Top.NakaneData.rayPoint]
      rw [hζfun, hEdef]
      exact div_norm_exp_pow_eq_one k θ (Work.EL.dynPhi c φ (g w)) t (by linarith) hu
    -- `dynPhi c φ ∘ g` is continuous on `C`
    have hDphi : ContinuousOn (Work.EL.dynPhi c φ) (Work.ParamRays.escapingSet c) := by
      refine hφ.1.congr ?_
      intro z hz
      have hzK : z ∉ Work.EL.K c := by
        rw [← Work.ParamRays.compl_filledJulia c] at hz
        exact hz
      exact Work.EL.dynPhi_of_notMem (φ := φ) hzK
    have hgu : ContinuousOn (fun w => Work.EL.dynPhi c φ (g w)) C := by
      have hgC : ContinuousOn g C := hcont.mono hCb
      have hMaps : Set.MapsTo g C (Work.ParamRays.escapingSet c) := by
        intro w hw
        rw [← Work.ParamRays.compl_filledJulia c]
        exact gK w hw
      exact hDphi.comp hgC hMaps
    have hune : ∀ w ∈ C, Work.EL.dynPhi c φ (g w) ≠ 0 := by
      intro w hw h0
      have h1 : 1 < ‖Work.EL.dynPhi c φ (g w)‖ :=
        Work.Top.NakaneData.Phi_mem_exteriorDisc hN (gK w hw)
      rw [h0, norm_zero] at h1
      linarith
    have hζcont : ContinuousOn ζ C := by
      have hfun : ζ = (fun w => Work.EL.dynPhi c φ (g w) / E) /
          (fun w => ((‖Work.EL.dynPhi c φ (g w) / E‖ : ℝ) : ℂ)) := by
        rw [hζfun]; ext w; rw [Pi.div_apply]
      rw [hfun]
      refine ContinuousOn.div (hgu.div_const E) ?_ ?_
      · exact Complex.continuous_ofReal.comp_continuousOn ((hgu.div_const E).norm)
      · intro w hw
        rw [Complex.ofReal_ne_zero]
        exact norm_ne_zero_iff.mpr (div_ne_zero (hune w hw) hEne)
    -- hence `ζ` is constant on `C`
    have hsubsing : (ζ '' C).Subsingleton :=
      preconnected_roots_subsingleton hn0 hconn ζ hζcont hζ1
    have hζconst : ∀ w ∈ C, ζ w = ζ w₀ := fun w hw =>
      hsubsing (Set.mem_image_of_mem ζ hw) (Set.mem_image_of_mem ζ hw₀)
    -- the constant value and the new angle
    have hζ0 : ζ w₀ ^ (4 ^ k) = 1 := hζ1 w₀ hw₀
    obtain ⟨m, hm⟩ := exists_int_exp_of_pow_eq_one hn0 hζ0
    set θ' : ℝ := (θ + (m : ℝ)) / ((4 : ℝ) ^ k) with hθ'def
    have hNm : (4 : ℝ) ^ k * θ' = θ + (m : ℝ) := by
      rw [hθ'def]
      exact mul_div_cancel₀ _ (pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0))
    have hEρ : E * ζ w₀ = Complex.exp (2 * ↑Real.pi * (θ' : ℂ) * Complex.I) := by
      rw [hm, hEdef, hθ'def]
      exact exp_mul_exp k θ m
    -- conclusion
    refine ⟨θ', ?_, m, ?_⟩
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hgwK := gK w hw
      have hunew := hune w hw
      have hζval : ζ w = (Work.EL.dynPhi c φ (g w) / E) / ‖Work.EL.dynPhi c φ (g w) / E‖ := by
        rw [hζfun]
      have hdir : E * ((Work.EL.dynPhi c φ (g w) / E) / ‖Work.EL.dynPhi c φ (g w) / E‖)
          = Complex.exp (2 * ↑Real.pi * (θ' : ℂ) * Complex.I) := by
        rw [← hζval, hζconst w hw]; exact hEρ
      have heq : Work.EL.dynPhi c φ (g w)
          = Work.Top.NakaneData.rayPoint θ' ‖Work.EL.dynPhi c φ (g w) / E‖ :=
        eq_rayPoint_of hEne hunew hdir
      -- the level is `> 1`
      obtain ⟨t, ht, hwt⟩ := (rayFacts w hw).2
      have hphiw : φ w = Work.Top.NakaneData.rayPoint θ t := by
        rw [← Work.EL.dynPhi_of_notMem (φ := φ) (rayFacts w hw).1]; exact hwt
      have hu : (Work.EL.dynPhi c φ (g w)) ^ (4 ^ k)
          = (t : ℂ) * Complex.exp (2 * ↑Real.pi * (θ : ℂ) * Complex.I) := by
        rw [hdyn w hw, hphiw, Work.Top.NakaneData.rayPoint]
      have hs : ‖Work.EL.dynPhi c φ (g w) / E‖ ^ (4 ^ k) = t := by
        rw [hEdef]
        exact norm_div_exp_pow k θ (Work.EL.dynPhi c φ (g w)) t (by linarith) hu
      have hlevel : 1 < ‖Work.EL.dynPhi c φ (g w) / E‖ := by
        by_contra hle
        push Not at hle
        have h2 : ‖Work.EL.dynPhi c φ (g w) / E‖ ^ (4 ^ k) ≤ 1 := by
          calc ‖Work.EL.dynPhi c φ (g w) / E‖ ^ (4 ^ k) ≤ 1 ^ (4 ^ k) :=
                pow_le_pow_left₀ (norm_nonneg _) hle _
            _ = 1 := one_pow _
        rw [hs] at h2
        linarith
      exact (Work.Top.NakaneData.mem_paramRay_iff hN).mpr
        ⟨hgwK, ‖Work.EL.dynPhi c φ (g w) / E‖, hlevel, heq⟩
    · rw [hNm]

end Work.LandLeaves
