import Mathlib
import Submission.Commons.NumberTheory.NumberField.exists_basis_coe_ringOfIntegers
import Submission.Commons.Algebra.MvPolynomial.univEval_eval
import Submission.Commons.Algebra.MvPolynomial.coeffMap_eval
import Submission.Commons.Algebra.MvPolynomial.coeffMap_totalDegree_eval
import Submission.Commons.Algebra.MvPolynomial.totalDegree_pderiv_le
import Submission.Commons.NumberTheory.NumberField.exists_wellPoised_point

/-!
# The polynomial certificate for well-poised points

Target lemma: `Commons.NumberTheory.NumberField.exists_certificate_poly`.

Given a number field `K` of degree `n = finrank ℚ K`, a `ℤ`-basis `ωb` of `𝓞 K`, and `r d : ℕ`
with `0 < d` and `(n-1)(r+1) < (d+r-1).choose r`, we produce a nonzero polynomial `Q` in the
coordinates `u : Fin n × Fin r → ℚ` of total degree `≤ d * n * (r+1)` such that, whenever
`Q u ≠ 0`, every pair `(a, b) ∈ K × K^r` is realised as the value and the gradient at the point
`ξ(u) = (∑ i, u (i,j) • ωb i)_j` of a polynomial `f ∈ ℚ[x₁,…,x_r]` of total degree `≤ d`.

* `jetLM r x` is the `ℚ`-linear jet map `f ↦ (∂ᵗ f (x))ₜ` landing in `Option (Fin r) → K ≅ K^{r+1}`.
* `pt ωb u` is the point `ξ(u)`.
* `basis_identity` expands a vector of `K` in a `ℚ`-basis `ωbQ` of `K`.
* `certificate_of_wellPoised` builds `Q` from a point `u₀` at which `jetLM` is surjective.
* The hard ingredient — that such a `u₀` exists under the hypothesis
  `(n-1)(r+1) < (d+r-1).choose r` — is the lemma
  `Commons.NumberTheory.NumberField.exists_wellPoised_point`.
-/

namespace Commons.NumberTheory.NumberField

open Module MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

/-- The jet evaluation map: `f ↦ ((∂ᵗ f)(x))_{t : Option (Fin r)}`. -/
noncomputable def jetLM (r : ℕ) (x : Fin r → K) :
    MvPolynomial (Fin r) ℚ →ₗ[ℚ] (Option (Fin r) → K) :=
  LinearMap.pi (fun t : Option (Fin r) =>
    (MvPolynomial.aeval x).toLinearMap.comp
      (Option.elim t LinearMap.id (fun j => (MvPolynomial.pderiv (R := ℚ) j).toLinearMap)))

lemma jetLM_apply (r : ℕ) (x : Fin r → K) (f : MvPolynomial (Fin r) ℚ) (t : Option (Fin r)) :
    jetLM r x f t = MvPolynomial.aeval x (Option.elim t f (fun j => MvPolynomial.pderiv j f)) := by
  cases t <;> simp [jetLM]

/-- The point of `K^r` encoded by the rational coordinates `u` in the `ℤ`-basis `ωb`. -/
noncomputable def pt {n r : ℕ} (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
    (u : Fin n × Fin r → ℚ) : Fin r → K :=
  fun j => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))

/-- `Jet t f` is `f` if `t = none` and `∂ⱼ f` if `t = some j`. -/
noncomputable def Jet (r : ℕ) (t : Option (Fin r)) (f : MvPolynomial (Fin r) ℚ) :
    MvPolynomial (Fin r) ℚ :=
  Option.elim t f (fun j => MvPolynomial.pderiv j f)

lemma jetLM_apply' (r : ℕ) (x : Fin r → K) (f : MvPolynomial (Fin r) ℚ) (t : Option (Fin r)) :
    jetLM r x f t = MvPolynomial.aeval x (Jet r t f) := by
  cases t <;> simp [jetLM, Jet]

/-- Expansion of a vector of `K` in the `ℚ`-basis `ωbQ`. -/
lemma basis_identity {n r : ℕ} (ωbQ : Module.Basis (Fin n) ℚ K) (z : Option (Fin r) → K) :
    z = ∑ s : Fin n × Option (Fin r), (ωbQ.coord s.1 (z s.2)) •
      (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K) := by
  funext t
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  have h : ∀ x : Fin n, (∑ y : Option (Fin r),
      (ωbQ.coord x (z y)) • (Pi.single y (ωbQ x) : Option (Fin r) → K) t)
        = (ωbQ.coord x (z t)) • ωbQ x := by
    intro x
    rw [Finset.sum_eq_single t]
    · rw [Pi.single_eq_same]
    · intro y _ hy; rw [Pi.single_eq_of_ne (Ne.symm hy), smul_zero]
    · intro h; exact absurd (Finset.mem_univ t) h
  exact (Eq.trans (Finset.sum_congr rfl fun x _ => h x) (ωbQ.sum_repr (z t))).symm

/-- `totalDegree` bound for a finite product. -/
lemma totalDegree_finsetProd_le {ι : Type*} {σ : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ ℚ) :
    (Finset.prod s f).totalDegree ≤ Finset.sum s (fun i => (f i).totalDegree) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_left ih _)

/-- The jet of a polynomial of total degree `≤ d` again has total degree `≤ d`. -/
lemma totalDegree_Jet_le (r : ℕ) (t : Option (Fin r)) (f : MvPolynomial (Fin r) ℚ) :
    (Jet r t f).totalDegree ≤ f.totalDegree := by
  cases t with
  | none => simp [Jet]
  | some j =>
      exact Commons.Algebra.MvPolynomial.totalDegree_pderiv_le f j

/-- **The certificate construction.**  Given a point `u₀` at which the jet map is surjective, there
is a certificate `Q`. -/
theorem certificate_of_wellPoised (n r d : ℕ) (hn : Module.finrank ℚ K = n)
    (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)) (hd : 0 < d)
    (ωbQ : Module.Basis (Fin n) ℚ K)
    (hωbQ : ∀ k, ωbQ k = ((ωb k : NumberField.RingOfIntegers K) : K))
    (u₀ : Fin n × Fin r → ℚ)
    (hu₀ : ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
      MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u₀ (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) f = g.1 ∧
      ∀ j : Fin r, MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u₀ (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) (MvPolynomial.pderiv j f) = g.2 j) :
    ∃ Q : MvPolynomial (Fin n × Fin r) ℚ, Q ≠ 0 ∧ Q.totalDegree ≤ d * n * (r + 1) ∧
      ∀ u : Fin n × Fin r → ℚ, MvPolynomial.eval u Q ≠ 0 →
        ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
          MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) f = g.1 ∧
          ∀ j : Fin r, MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) (MvPolynomial.pderiv j f) = g.2 j := by
  classical
  let ωbK : Fin n → K := fun i => ((ωb i : NumberField.RingOfIntegers K) : K)
  obtain ⟨ρ, hρdeg, hρeval⟩ := Commons.Algebra.MvPolynomial.univEval_eval (K := K) ωbK
  have hcoeff : ∀ k : Fin n, ∃ Φ : MvPolynomial (Fin n × Fin r) K →ₗ[ℚ] MvPolynomial (Fin n × Fin r) ℚ,
      (∀ p, (Φ p).totalDegree ≤ p.totalDegree) ∧
      ∀ (p : MvPolynomial (Fin n × Fin r) K) (u : Fin n × Fin r → ℚ),
        MvPolynomial.eval u (Φ p) = ωbQ.coord k (MvPolynomial.eval (fun s => (u s : K)) p) :=
    fun k => Commons.Algebra.MvPolynomial.coeffMap_totalDegree_eval (ωbQ.coord k)
  let Φ : Fin n → (MvPolynomial (Fin n × Fin r) K →ₗ[ℚ] MvPolynomial (Fin n × Fin r) ℚ) :=
    fun k => Classical.choose (hcoeff k)
  have hΦdeg : ∀ (k : Fin n) (p : MvPolynomial (Fin n × Fin r) K),
      ((Φ k) p).totalDegree ≤ p.totalDegree :=
    fun k => (Classical.choose_spec (hcoeff k)).1
  have hΦeval : ∀ (k : Fin n) (p : MvPolynomial (Fin n × Fin r) K) (u : Fin n × Fin r → ℚ),
      MvPolynomial.eval u ((Φ k) p) = ωbQ.coord k (MvPolynomial.eval (fun s => (u s : K)) p) :=
    fun k => (Classical.choose_spec (hcoeff k)).2
  have hw : ∀ w : Option (Fin r) → K, ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
      jetLM r (pt ωb u₀) f = w := by
    intro w
    obtain ⟨f, hd1, hd2, hd3⟩ := hu₀ (w none, fun j => w (some j))
    refine ⟨f, hd1, ?_⟩
    funext t
    cases t with
    | none =>
        rw [jetLM_apply]
        exact hd2
    | some j =>
        rw [jetLM_apply]
        exact hd3 j
  have hex : ∀ s : Fin n × Option (Fin r), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
      jetLM r (pt ωb u₀) f = (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K) := by
    intro s
    obtain ⟨f, hf1, hf2⟩ := hw (Pi.single s.2 (ωbQ s.1))
    exact ⟨f, hf1, hf2⟩
  let f₀ : (Fin n × Option (Fin r)) → MvPolynomial (Fin r) ℚ :=
    fun s => Classical.choose (hex s)
  have hf₀1 : ∀ s, (f₀ s).totalDegree ≤ d :=
    fun s => (Classical.choose_spec (hex s)).1
  have hf₀jet : ∀ s, jetLM r (pt ωb u₀) (f₀ s) = (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K) :=
    fun s => (Classical.choose_spec (hex s)).2
  let Mp : Matrix (Fin n × Option (Fin r)) (Fin n × Option (Fin r))
      (MvPolynomial (Fin n × Fin r) ℚ) := fun s s' => Φ s.1 (ρ (Jet r s.2 (f₀ s')))
  have hMval : ∀ (u : Fin n × Fin r → ℚ) (s s' : Fin n × Option (Fin r)),
      (Mp.map (MvPolynomial.eval u)) s s' = ωbQ.coord s.1 ((jetLM r (pt ωb u) (f₀ s')) s.2) := by
    intro u s s'
    rw [Matrix.map_apply, hΦeval s.1 _ u, hρeval u, jetLM_apply']
    congr 1
  refine ⟨Mp.det, ?_, ?_, ?_⟩
  · -- Q ≠ 0, by evaluation at u₀
    intro hQ
    have h1 : (Mp.map (MvPolynomial.eval u₀)).det = 0 := by
      have hdet := RingHom.map_det (MvPolynomial.eval u₀) Mp
      rw [hQ, map_zero] at hdet
      simpa using hdet.symm
    have h2 : (Mp.map (MvPolynomial.eval u₀)) = 1 := by
      ext s s'
      rw [hMval u₀ s s', hf₀jet s', Matrix.one_apply]
      by_cases hs : s.2 = s'.2 <;> by_cases hk : s.1 = s'.1
      · rw [hs, Pi.single_eq_same, if_pos (Prod.ext hk hs), hk, ωbQ.coord_apply,
          Basis.repr_self]
        simp
      · rw [hs, Pi.single_eq_same, ωbQ.coord_apply, Basis.repr_self,
          Finsupp.single_apply, if_neg (Ne.symm hk), if_neg]
        intro hc; exact hk (congrArg Prod.fst hc)
      · rw [Pi.single_eq_of_ne hs, map_zero, if_neg]
        intro hc; exact hs (congrArg Prod.snd hc)
      · rw [Pi.single_eq_of_ne hs, map_zero, if_neg]
        intro hc; exact hs (congrArg Prod.snd hc)
    rw [h2, Matrix.det_one] at h1
    exact one_ne_zero h1
  · -- degree bound
    rw [Matrix.det_apply']
    refine MvPolynomial.totalDegree_finsetSum_le fun σ _ => ?_
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hc : (↑↑(Equiv.Perm.sign σ) : MvPolynomial (Fin n × Fin r) ℚ).totalDegree = 0 := by
      rw [show (↑↑(Equiv.Perm.sign σ) : MvPolynomial (Fin n × Fin r) ℚ)
          = MvPolynomial.C (↑↑(Equiv.Perm.sign σ) : ℚ) from rfl, MvPolynomial.totalDegree_C]
    rw [hc, Nat.zero_add]
    calc (∏ i : Fin n × Option (Fin r), Mp (σ i) i).totalDegree
        ≤ ∑ i : Fin n × Option (Fin r), (Mp (σ i) i).totalDegree := totalDegree_finsetProd_le _ _
      _ ≤ ∑ _i : Fin n × Option (Fin r), d := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact le_trans (hΦdeg _ _)
            (le_trans (hρdeg _) (le_trans (totalDegree_Jet_le r (σ i).2 (f₀ i)) (hf₀1 i)))
      _ = d * n * (r + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_option, Fintype.card_fin, smul_eq_mul]
          ring
  · -- main implication
    intro u hu g
    have hunit : IsUnit (Mp.map (MvPolynomial.eval u)).det := by
      rw [show (Mp.map (MvPolynomial.eval u)).det = MvPolynomial.eval u Mp.det from
        (RingHom.map_det (MvPolynomial.eval u) Mp).symm]
      exact isUnit_iff_ne_zero.mpr hu
    have hunit2 : IsUnit (Mp.map (MvPolynomial.eval u)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hunit
    obtain ⟨N, hN⟩ := hunit2.exists_right_inv
    let w : Option (Fin r) → K := fun t => Option.elim t g.1 g.2
    let aa : Fin n × Option (Fin r) → ℚ := fun s => ωbQ.coord s.1 (w s.2)
    let c : Fin n × Option (Fin r) → ℚ := N.mulVec aa
    have hMc : (Mp.map (MvPolynomial.eval u)).mulVec c = aa := by
      rw [show c = N.mulVec aa from rfl, Matrix.mulVec_mulVec, hN, Matrix.one_mulVec]
    have hterm : ∀ s' : Fin n × Option (Fin r),
        jetLM r (pt ωb u) (c s' • f₀ s') = ∑ s : Fin n × Option (Fin r),
          (c s' * (Mp.map (MvPolynomial.eval u)) s s') •
            (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K) := by
      intro s'
      rw [map_smul, basis_identity ωbQ (jetLM r (pt ωb u) (f₀ s')), Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hMval u s s', smul_smul]
    have hterm2 : (∑ s : Fin n × Option (Fin r), aa s •
        (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K)) = ∑ s : Fin n × Option (Fin r),
          ((Mp.map (MvPolynomial.eval u)).mulVec c s) •
            (Pi.single s.2 (ωbQ s.1) : Option (Fin r) → K) :=
      Finset.sum_congr rfl fun s _ => by rw [congrFun hMc.symm s]
    have key : jetLM r (pt ωb u) (∑ s', c s' • f₀ s') = w := by
      rw [map_sum, basis_identity ωbQ w, hterm2,
        Finset.sum_congr rfl (fun s' _ => hterm s'), Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      exact Finset.sum_congr rfl
        (fun i (_ : i ∈ Finset.univ) => mul_comm (c i) ((Mp.map (MvPolynomial.eval u)) s i))
    refine ⟨∑ s', c s' • f₀ s', ?_, ?_, ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun s' _ => ?_
      exact le_trans (MvPolynomial.totalDegree_smul_le _ _) (hf₀1 s')
    · have h := congrFun key none
      rw [jetLM_apply] at h
      rw [show (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) •
          (((ωb i : NumberField.RingOfIntegers K) : K))) = pt ωb u from rfl]
      simpa [Jet, w] using h
    · intro j
      have h := congrFun key (some j)
      rw [jetLM_apply] at h
      rw [show (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) •
          (((ωb i : NumberField.RingOfIntegers K) : K))) = pt ωb u from rfl]
      simpa [Jet, w] using h

open Commons.Algebra.MvPolynomial in
/-- **The certificate lemma.** -/
theorem exists_certificate_poly (K : Type*) [Field K] [NumberField K] (n r d : ℕ)
    (hn : Module.finrank ℚ K = n) (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
    (hd : 0 < d) (h : (n - 1) * (r + 1) < (d + r - 1).choose r) :
    ∃ Q : MvPolynomial (Fin n × Fin r) ℚ, Q ≠ 0 ∧ Q.totalDegree ≤ d * n * (r + 1) ∧
      ∀ u : Fin n × Fin r → ℚ, MvPolynomial.eval u Q ≠ 0 →
        ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
          MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) f = g.1 ∧
          ∀ j : Fin r, MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) (MvPolynomial.pderiv j f) = g.2 j := by
  obtain ⟨ωbQ, hωbQ⟩ := exists_basis_coe_ringOfIntegers K ωb hn
  obtain ⟨u₀, hu₀⟩ := exists_wellPoised_point K n r d hn ωb hd h
  obtain ⟨Q, hQ1, hQ2, hQ3⟩ := certificate_of_wellPoised n r d hn ωb hd ωbQ hωbQ u₀ hu₀
  exact ⟨Q, hQ1, hQ2, hQ3⟩

end Commons.NumberTheory.NumberField
