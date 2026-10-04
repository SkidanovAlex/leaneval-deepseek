import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.psi_estimates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Auxiliary lemmas for the Parseval/`Σ Fᵢ² = 1` estimate

* `parseval_orthonormal`: for an orthonormal family `e : Fin n → V` in a finite-dimensional real
  inner product space with `n = finrank ℝ V`, `∑ i, ⟪e i, u⟫² = ⟪u, u⟫`.
* `sum_sq_close_of_models`: the arithmetic core: if `a` is within `K` of a model `m` whose squares
  sum to `1`, and both `a` and `m` are bounded by `1` in absolute value, then
  `|∑ aᵢ² - 1| ≤ 4 N K`.
* `model_sum_eq_one`: the evaluation of the model along the ray, from `InitData`. -/

/-- **Parseval for an orthonormal family of full size.** -/
theorem parseval_orthonormal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (e : Fin n → V)
    (hON : ∀ i j : Fin n, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hcard : n = Module.finrank ℝ V) (u : V) :
    ∑ i : Fin n, (Inner.inner ℝ (e i) u) ^ 2 = Inner.inner ℝ u u := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hcard.symm
    rw [Subsingleton.elim u 0]
    simp
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hv : Orthonormal ℝ e := orthonormal_iff_ite.mpr hON
    have hcard' : Fintype.card (Fin n) = Module.finrank ℝ V := by simpa using hcard
    let b : Module.Basis (Fin n) ℝ V := basisOfOrthonormalOfCardEqFinrank hv hcard'
    have hb : Orthonormal ℝ (b : Fin n → V) := by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hv
    let ob : OrthonormalBasis (Fin n) ℝ V := b.toOrthonormalBasis hb
    have hob : (ob : Fin n → V) = e := by
      rw [show (ob : Fin n → V) = (b : Fin n → V) from
        Module.Basis.coe_toOrthonormalBasis b hb,
        coe_basisOfOrthonormalOfCardEqFinrank]
    have h1 : ∑ i : Fin n, (Inner.inner ℝ (ob i) u) ^ 2 = ‖u‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right ob u
    simp only [hob] at h1
    rw [h1, real_inner_self_eq_norm_sq]

/-- **The arithmetic core.**  If `a i` is within `K` of a model `m i`, if `∑ mᵢ² = 1` and if both
`a` and `m` are bounded by `1`, then `∑ aᵢ²` is within `4 N K` of `1`. -/
theorem sum_sq_close_of_models {N : ℕ} {a m : Fin N → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (ha : ∀ i, |a i| ≤ 1) (hm : ∀ i, |m i| ≤ 1)
    (hdev : ∀ i, |a i - m i| ≤ K) (hmsum : ∑ i, m i ^ 2 = 1) :
    |(∑ i, a i ^ 2) - 1| ≤ 4 * (N : ℝ) * K := by
  have h1 : (∑ i, a i ^ 2) - 1 = ∑ i, (a i ^ 2 - m i ^ 2) := by
    rw [Finset.sum_sub_distrib, hmsum]
  rw [h1]
  have h2 : ∀ i : Fin N, |a i ^ 2 - m i ^ 2| ≤ 2 * K := by
    intro i
    have h3 : a i ^ 2 - m i ^ 2 = (a i - m i) * (a i + m i) := by ring
    rw [h3, abs_mul]
    have h4 : |a i + m i| ≤ 2 := by
      calc |a i + m i| ≤ |a i| + |m i| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (ha i) (hm i)
        _ = 2 := by norm_num
    calc |a i - m i| * |a i + m i| ≤ K * 2 :=
          mul_le_mul (hdev i) h4 (abs_nonneg _) hK
      _ = 2 * K := by ring
  calc |∑ i, (a i ^ 2 - m i ^ 2)| ≤ ∑ i, |a i ^ 2 - m i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, 2 * K := Finset.sum_le_sum (fun i _ => h2 i)
    _ = (N : ℝ) * (2 * K) := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = 2 * (N : ℝ) * K := by ring
    _ ≤ 4 * (N : ℝ) * K := by
        have : (0:ℝ) ≤ (N:ℝ) * K := mul_nonneg (Nat.cast_nonneg N) hK
        linarith

/-- **The model along the ray.**  With `fᵢ = fFam hmet p e i` and `InitData` at `p`, the model
values `fᵢ(p) cos s + ⟪∇fᵢ(p),u⟫ sin s` are bounded by `1` and their squares sum to `1`. -/
theorem model_sum_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {n : ℕ} {p : M} {e : Fin n → TangentSpace I p}
    {u : TangentSpace I p} {s : ℝ}
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hON : ∀ i j : Fin n, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hu : Inner.inner ℝ u u = 1)
    (hpar : ∑ j : Fin n, (Inner.inner ℝ (e j) u) ^ 2 = 1) :
    (∀ i : Fin (n + 1), |fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos s
        + Inner.inner ℝ (rgrad (I := I) (M := M)
            (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin s| ≤ 1) ∧
    (∑ i : Fin (n + 1), (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos s
        + Inner.inner ℝ (rgrad (I := I) (M := M)
            (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin s) ^ 2) = 1 := by
  classical
  rw [InitData] at hinit
  obtain ⟨h0v, h0g, hrest⟩ := hinit
  have hq0 : qpt (I := I) (M := M) (cov := cov) hmet p e 0 = p := by
    rw [qpt, dirv, Fin.cases_zero, smul_zero]
    exact Submission.GlobalExp.GExp_zero hmet p
  have hv0 : fFam (I := I) (M := M) (cov := cov) hmet p e 0 p = 1 := by
    show fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e 0) p = 1
    rw [hq0]; exact h0v
  have hg0 : rgrad (I := I) (M := M)
      (fFam (I := I) (M := M) (cov := cov) hmet p e 0) p = 0 := by
    show rgrad (I := I) (M := M)
      (fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e 0)) p = 0
    rw [hq0]; exact h0g
  have hvS : ∀ i : Fin n,
      fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i) p = 0 := by
    intro i
    show fcos (I := I) (M := M)
      (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)) p = 0
    exact (hrest i).1
  have hgS : ∀ i : Fin n, rgrad (I := I) (M := M)
      (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)) p = e i := by
    intro i
    show rgrad (I := I) (M := M) (fcos (I := I) (M := M)
      (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i))) p = e i
    exact (hrest i).2
  constructor
  · intro i
    by_cases hi : i = 0
    · rw [hi, hv0, hg0]
      simpa using Real.abs_cos_le_one s
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
      rw [hvS j, hgS j]
      have hcs : |Inner.inner ℝ (e j) u| ≤ 1 := by
        refine le_trans (abs_real_inner_le_norm (e j) u) ?_
        have h2 : ‖e j‖ = 1 := by
          have h := hON j j
          rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
          nlinarith [norm_nonneg (e j)]
        have h3 : ‖u‖ = 1 := by
          have h := real_inner_self_eq_norm_sq u
          rw [hu] at h
          nlinarith [norm_nonneg u]
        rw [h2, h3, mul_one]
      have hsimp : |0 * Real.cos s + Inner.inner ℝ (e j) u * Real.sin s|
          = |Inner.inner ℝ (e j) u * Real.sin s| := by simp
      rw [hsimp, abs_mul]
      exact le_trans (mul_le_mul hcs (Real.abs_sin_le_one s) (abs_nonneg _) zero_le_one)
        (by norm_num)
  · rw [Fin.sum_univ_succ]
    have h0 : fFam (I := I) (M := M) (cov := cov) hmet p e 0 p * Real.cos s
        + Inner.inner ℝ (rgrad (I := I) (M := M)
            (fFam (I := I) (M := M) (cov := cov) hmet p e 0) p) u * Real.sin s
        = Real.cos s := by
      rw [hv0, hg0]; simp
    have hS : ∀ i : Fin n, fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i) p * Real.cos s
        + Inner.inner ℝ (rgrad (I := I) (M := M)
            (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)) p) u * Real.sin s
        = Inner.inner ℝ (e i) u * Real.sin s := by
      intro i
      rw [hvS i, hgS i]; simp
    rw [h0]
    rw [show (∑ i : Fin n, (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i) p
            * Real.cos s + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)) p) u * Real.sin s) ^ 2)
        = ∑ i : Fin n, (Inner.inner ℝ (e i) u * Real.sin s) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [hS i])]
    rw [show (∑ i : Fin n, (Inner.inner ℝ (e i) u * Real.sin s) ^ 2)
        = Real.sin s ^ 2 * (∑ i : Fin n, (Inner.inner ℝ (e i) u) ^ 2) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [hpar, mul_one]
    exact Real.cos_sq_add_sin_sq s

/-- **The Parseval/`Σ Fᵢ² = 1` estimate along a ray, in the "everything stays smooth" case.**
With `qᵢ = qpt hmet p e i`, `fᵢ = fFam hmet p e i = cos ∘ d(qᵢ,·)`, `Fᵢ = ψ ∘ fᵢ`, `x = GExp p (s • u)`
on a unit-speed ray from `p`, initial data `InitData` at `p`, `e` an **orthonormal basis**
(`e : Fin (finrank ℝ E) → T_pM`, the same indexing as in `gram_pointwise2`) and `u` a unit vector,
*if* the model comparison `|fᵢ(x) - (fᵢ(p) cos s + ⟪∇fᵢ(p),u⟫ sin s)| ≤ 2ε₁s` and the non-clamping
`-1+2c ≤ fᵢ(x)` hold for every `i`, then the squared sum is within `100(n+2)(ε₁π + √c)` of `1`.

(The mathematics is: `ψ = id` at those points, the models are `cos s` and `⟪eᵢ,u⟫ sin s` by
`InitData`, and `cos²s + Σ_{i≥1}⟪eᵢ,u⟫² sin²s = cos²s + sin²s = 1` by Parseval.) -/
theorem sum_rule_good_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {p x : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p} {u : TangentSpace I p}
    {s c ε₁ : ℝ}
    (hc : 0 < c) (hε₁ : 0 ≤ ε₁) (hu : Inner.inner ℝ u u = 1) (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    (hx : Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = x)
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ t : ℝ, 0 ≤ deriv ψ t ∧ deriv ψ t ≤ 2) ∧
      (∀ t : ℝ, -1 + 2 * c ≤ t → ψ t = t) ∧ (∀ t : ℝ, t ≤ -1 + c → ψ t = -1 + c))
    (hstay : ∀ i : Fin (Module.finrank ℝ E + 1),
      -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i x)
    (hmodel : ∀ i : Fin (Module.finrank ℝ E + 1),
      |fFam (I := I) (M := M) (cov := cov) hmet p e i x
        - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos s
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin s)|
        ≤ 2 * ε₁ * s) :
    |(∑ i, (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x)) ^ 2) - 1|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + Real.sqrt c) := by
  classical
  -- `ψ` is the identity on the values that occur
  have hpsi : ∀ i : Fin (Module.finrank ℝ E + 1),
      ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x)
        = fFam (I := I) (M := M) (cov := cov) hmet p e i x :=
    fun i => hψ.2.2.2.1 _ (hstay i)
  have hsumpsi : (∑ i : Fin (Module.finrank ℝ E + 1),
        (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x)) ^ 2)
      = ∑ i : Fin (Module.finrank ℝ E + 1),
        (fFam (I := I) (M := M) (cov := cov) hmet p e i x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [hpsi i])
  rw [hsumpsi]
  -- Parseval for the orthonormal family `e`
  have hcard : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I p) :=
    (tangentSpaceCastModel I p).toLinearEquiv.finrank_eq.symm
  have hpar : ∑ j : Fin (Module.finrank ℝ E), (Inner.inner ℝ (e j) u) ^ 2 = 1 := by
    have h := parseval_orthonormal (e := e) (hON := hON) (hcard := hcard) (u := u)
    rw [hu] at h
    exact h
  -- the model
  obtain ⟨hm1, hmsum⟩ := model_sum_eq_one (I := I) (M := M) (cov := cov) hmet
    (p := p) (e := e) (u := u) (s := s) hinit hON hu hpar
  have ha : ∀ i : Fin (Module.finrank ℝ E + 1),
      |fFam (I := I) (M := M) (cov := cov) hmet p e i x| ≤ 1 := by
    intro i
    have h : fFam (I := I) (M := M) (cov := cov) hmet p e i x
        = Real.cos (rdist (I := I) (qpt (I := I) (M := M) (cov := cov) hmet p e i) x) := rfl
    rw [h]
    exact Real.abs_cos_le_one _
  have hdev : ∀ i : Fin (Module.finrank ℝ E + 1),
      |fFam (I := I) (M := M) (cov := cov) hmet p e i x
        - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos s
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin s)|
        ≤ 2 * ε₁ * s := fun i => hmodel i
  have hK : (0 : ℝ) ≤ 2 * ε₁ * s := mul_nonneg (mul_nonneg (by norm_num) hε₁) hs0
  have hmain := sum_sq_close_of_models (N := Module.finrank ℝ E + 1)
    (a := fun i => fFam (I := I) (M := M) (cov := cov) hmet p e i x)
    (m := fun i => fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos s
      + Inner.inner ℝ (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin s)
    (K := 2 * ε₁ * s) hK ha hm1 hdev hmsum
  refine le_trans hmain ?_
  have hcast : ((Module.finrank ℝ E + 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have key : 4 * ((Module.finrank ℝ E + 1 : ℕ) : ℝ) * (2 * ε₁ * s)
      = 8 * ((Module.finrank ℝ E : ℝ) + 1) * (ε₁ * s) := by
    rw [hcast]; ring
  rw [key]
  have hF : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h1 : (0 : ℝ) ≤ ε₁ * s := mul_nonneg hε₁ hs0
  have h2 : ε₁ * s ≤ ε₁ * Real.pi := mul_le_mul_of_nonneg_left hsπ hε₁
  have h3 : (0 : ℝ) ≤ ε₁ * Real.pi := mul_nonneg hε₁ hπ
  have h4 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hA : (0 : ℝ) ≤ 8 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
  have hB : (0 : ℝ) ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) := by linarith
  have s1 : 8 * ((Module.finrank ℝ E : ℝ) + 1) * (ε₁ * s)
      ≤ 8 * ((Module.finrank ℝ E : ℝ) + 1) * (ε₁ * Real.pi) :=
    mul_le_mul_of_nonneg_left h2 hA
  have s2 : 8 * ((Module.finrank ℝ E : ℝ) + 1) * (ε₁ * Real.pi)
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi) := by
    have hle : 8 * ((Module.finrank ℝ E : ℝ) + 1)
        ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) := by linarith
    exact mul_le_mul_of_nonneg_right hle h3
  have s3 : 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi)
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + Real.sqrt c) :=
    mul_le_mul_of_nonneg_left (by linarith [h4]) hB
  exact le_trans s1 (le_trans s2 s3)

end Work.Diff.C
