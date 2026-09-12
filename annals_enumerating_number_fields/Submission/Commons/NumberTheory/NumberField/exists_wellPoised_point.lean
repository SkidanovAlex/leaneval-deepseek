import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Flat.TorsionFree
import Submission.Commons.NumberTheory.NumberField.exists_basis_coe_ringOfIntegers
import Submission.Commons.NumberTheory.NumberField.card_algHom_eq_finrank
import Submission.Commons.NumberTheory.NumberField.eq_zero_of_forall_ringHom_eq_zero
import Submission.Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le
import Submission.Commons.Algebra.MvPolynomial.exists_points_eval_surjective

namespace Commons.NumberTheory.NumberField

open MvPolynomial Module

/-- The matrix of the embeddings of a `ℚ`-basis of a number field `K` in `ℂ` is invertible. -/
theorem embeddingsMatrixReindex_det_ne_zero (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (b : Module.Basis (Fin n) ℚ K) (e : Fin n ≃ (K →ₐ[ℚ] ℂ)) :
    (Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => b i) e).det ≠ 0 := by
  set D := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => b i) e with hD
  have h1 : (Algebra.traceMatrix ℚ (fun i => b i)).map (algebraMap ℚ ℂ) = D * D.transpose :=
    Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans ℚ ℂ (fun i => b i) e
  have h2 : (Algebra.traceMatrix ℚ (fun i => b i)).det = Algebra.discr ℚ (fun i => b i) :=
    (Algebra.discr_def ℚ (fun i => b i)).symm
  have h3 : Algebra.discr ℚ (fun i => b i) ≠ 0 := Algebra.discr_not_zero_of_basis ℚ b
  have key : (algebraMap ℚ ℂ) (Algebra.discr ℚ (fun i => b i)) = D.det * D.det := by
    rw [← h2, RingHom.map_det]
    change ((Algebra.traceMatrix ℚ (fun i => b i)).map (algebraMap ℚ ℂ)).det = D.det * D.det
    rw [h1, Matrix.det_mul, Matrix.det_transpose]
  exact fun h => h3 ((algebraMap ℚ ℂ).injective (by rw [key, h, mul_zero, map_zero]))

variable {K : Type*} [Field K] [NumberField K]
variable {n r d : ℕ}

/-- The point of `K^r` encoded by `u` in the `ℚ`-basis `B`. -/
noncomputable def wpPt (B : Module.Basis (Fin n) ℚ K) (u : Fin n × Fin r → ℚ) : Fin r → K :=
  fun j => ∑ i : Fin n, (u (i, j) : ℚ) • B i

/-- The corresponding conjugate configuration. -/
noncomputable def wpConf (B : Module.Basis (Fin n) ℚ K) (e : Fin n ≃ (K →ₐ[ℚ] ℂ))
    (u : Fin n × Fin r → ℚ) (k : Fin n) : Fin r → ℂ :=
  fun j => ∑ i : Fin n, ((u (i, j) : ℚ) : ℂ) * (e k) (B i)

theorem wpPt_embeddings (B : Module.Basis (Fin n) ℚ K) (e : Fin n ≃ (K →ₐ[ℚ] ℂ))
    (u : Fin n × Fin r → ℚ) (k : Fin n) :
    (e k).comp (MvPolynomial.aeval (wpPt B u)) = MvPolynomial.aeval (wpConf B e u k) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  simp only [wpPt, wpConf]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Algebra.smul_def, map_mul]
  simp

/-- The `ℚ`-linear jet map at `wpPt B u`. -/
noncomputable def wpJMap (B : Module.Basis (Fin n) ℚ K) (u : Fin n × Fin r → ℚ) :
    MvPolynomial (Fin r) ℚ →ₗ[ℚ] (Option (Fin r) → K) :=
  LinearMap.pi (fun t : Option (Fin r) =>
    (MvPolynomial.aeval (wpPt B u)).toLinearMap.comp
      (Option.elim t LinearMap.id (fun j => (MvPolynomial.pderiv (R := ℚ) j).toLinearMap)))

lemma wpJMap_apply (B : Module.Basis (Fin n) ℚ K) (u : Fin n × Fin r → ℚ)
    (f : MvPolynomial (Fin r) ℚ) (t : Option (Fin r)) :
    wpJMap B u f t =
      MvPolynomial.aeval (wpPt B u) (Option.elim t f (fun j => MvPolynomial.pderiv j f)) := by
  cases t <;> rfl

/-- The bounded-degree `ℚ`-linear jet map at `wpPt B u`. -/
noncomputable def wpJMapBdd (d : ℕ) (B : Module.Basis (Fin n) ℚ K) (u : Fin n × Fin r → ℚ) :
    MvPolynomial.restrictTotalDegree (Fin r) ℚ d →ₗ[ℚ] (Option (Fin r) → K) :=
  (wpJMap B u).comp (MvPolynomial.restrictTotalDegree (Fin r) ℚ d).subtype

lemma wpJMapBdd_apply (B : Module.Basis (Fin n) ℚ K) (u : Fin n × Fin r → ℚ)
    (x : MvPolynomial.restrictTotalDegree (Fin r) ℚ d) :
    wpJMapBdd d B u x = wpJMap B u x.1 := rfl

/-- The `ℂ`-linear jet map at a configuration. -/
noncomputable def wpCJet (U : Fin n → Fin r → ℂ) :
    MvPolynomial (Fin r) ℂ →ₗ[ℂ] (Fin n → Option (Fin r) → ℂ) :=
  LinearMap.pi (fun k : Fin n => LinearMap.pi (fun t : Option (Fin r) =>
    (MvPolynomial.aeval (U k)).toLinearMap.comp
      (Option.elim t LinearMap.id (fun j => (MvPolynomial.pderiv (R := ℂ) j).toLinearMap))))

lemma wpCJet_apply (U : Fin n → Fin r → ℂ) (f : MvPolynomial (Fin r) ℂ) (k : Fin n)
    (t : Option (Fin r)) :
    wpCJet U f k t = MvPolynomial.aeval (U k) (Option.elim t f (fun j => MvPolynomial.pderiv j f)) := by
  cases t <;> rfl

/-- The bounded-degree `ℂ`-linear jet map at a configuration. -/
noncomputable def wpCJetBdd (d : ℕ) (U : Fin n → Fin r → ℂ) :
    MvPolynomial.restrictTotalDegree (Fin r) ℂ d →ₗ[ℂ] (Fin n → Option (Fin r) → ℂ) :=
  (wpCJet U).comp (MvPolynomial.restrictTotalDegree (Fin r) ℂ d).subtype

lemma wpCJetBdd_apply (U : Fin n → Fin r → ℂ)
    (x : MvPolynomial.restrictTotalDegree (Fin r) ℂ d) :
    wpCJetBdd d U x = wpCJet U x.1 := rfl

/-- Conjugation of the `ℚ`-jet map is the `ℂ`-jet map at the conjugate configuration. -/
noncomputable def wpIota (e : Fin n ≃ (K →ₐ[ℚ] ℂ)) :
    (Option (Fin r) → K) →ₗ[ℚ] (Fin n → Option (Fin r) → ℂ) :=
  LinearMap.pi (fun k : Fin n => LinearMap.pi (fun t : Option (Fin r) =>
    (e k).toLinearMap.comp (LinearMap.proj t)))

lemma wpIota_apply (e : Fin n ≃ (K →ₐ[ℚ] ℂ)) (z : Option (Fin r) → K) (k : Fin n)
    (t : Option (Fin r)) : wpIota e z k t = (e k) (z t) := rfl

theorem wpIota_wpJMap (B : Module.Basis (Fin n) ℚ K) (e : Fin n ≃ (K →ₐ[ℚ] ℂ))
    (u : Fin n × Fin r → ℚ) (f : MvPolynomial (Fin r) ℚ) :
    wpIota e (wpJMap B u f) = wpCJet (wpConf B e u) (f.map (algebraMap ℚ ℂ)) := by
  funext k t
  rw [wpIota_apply, wpJMap_apply, wpCJet_apply]
  have key := DFunLike.congr_fun (wpPt_embeddings B e u k)
  cases t with
  | none =>
    rw [Option.elim_none, Option.elim_none]
    rw [MvPolynomial.aeval_map_algebraMap ℂ (wpConf B e u k) f]
    exact key f
  | some j =>
    rw [Option.elim_some, Option.elim_some]
    rw [MvPolynomial.pderiv_map (φ := algebraMap ℚ ℂ) (f := f) (i := j),
      MvPolynomial.aeval_map_algebraMap ℂ (wpConf B e u k) (MvPolynomial.pderiv j f)]
    exact key (MvPolynomial.pderiv j f)

/-- A nonzero polynomial over `ℂ` has a rational point where it is nonzero. -/
lemma exists_rat_eval_ne_zero {N : ℕ} (p : MvPolynomial (Fin N) ℂ) (hp : p ≠ 0) :
    ∃ u : Fin N → ℚ, MvPolynomial.eval (fun i => ((u i : ℚ) : ℂ)) p ≠ 0 := by
  obtain ⟨u, -, hu⟩ :=
    Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le (F := ℂ) p hp le_rfl
  exact ⟨fun i => (u i : ℚ), by simpa using hu⟩

/-- A nonzero polynomial over `ℂ` in any finite set of variables has a rational point where it is
nonzero. -/
lemma exists_rat_eval_ne_zero' {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (hp : p ≠ 0) :
    ∃ u : σ → ℚ, MvPolynomial.eval (fun i => ((u i : ℚ) : ℂ)) p ≠ 0 := by
  obtain ⟨k, f, hf, q, hpq⟩ := MvPolynomial.exists_fin_rename p
  have hqne : q ≠ 0 := by
    rintro rfl
    exact hp (by rw [hpq, map_zero])
  obtain ⟨u, -, hu⟩ :=
    Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le (F := ℂ) q hqne le_rfl
  refine ⟨fun i => Function.extend f (fun i => (u i : ℚ)) 0 i, ?_⟩
  have hcomp : ((fun i : σ => ((Function.extend f (fun i => (u i : ℚ)) 0 i : ℚ) : ℂ)) ∘ f)
      = fun i : Fin k => (u i : ℂ) := by
    funext i
    rw [Function.comp_apply, hf.extend_apply]
    push_cast
    rfl
  rw [hpq, MvPolynomial.eval_rename, hcomp]
  exact hu

/-- The total degree does not increase under a ring homomorphism of the coefficient ring. -/
lemma totalDegree_map_le {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (p.map f).totalDegree ≤ p.totalDegree := by
  have hsum : p.map f = ∑ m ∈ p.support, MvPolynomial.monomial m (f (MvPolynomial.coeff m p)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.map_monomial]
  rw [hsum]
  exact MvPolynomial.totalDegree_finsetSum_le (s := p.support)
    (f := fun m => MvPolynomial.monomial m (f (MvPolynomial.coeff m p))) (d := p.totalDegree)
    (fun m hm => le_trans (MvPolynomial.totalDegree_monomial_le m _)
      (MvPolynomial.le_totalDegree hm))

/-- `aeval` then `aeval` is `aeval` along the composite. -/
lemma aeval_aeval_comp {σ τ : Type*} (x : τ → ℂ) (y : σ → MvPolynomial τ ℂ)
    (p : MvPolynomial σ ℂ) :
    MvPolynomial.aeval x (MvPolynomial.aeval y p) =
      MvPolynomial.aeval (fun i => MvPolynomial.aeval x (y i)) p := by
  have h : ((MvPolynomial.aeval x).comp (MvPolynomial.aeval y))
      = MvPolynomial.aeval (fun i => MvPolynomial.aeval x (y i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h p

/-- The `ℂ`-span of a `ℚ`-subspace has `ℂ`-dimension at most its `ℚ`-dimension. -/
lemma finrank_span_le_finrank (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℚ E]
    [IsScalarTower ℚ ℂ E] [Module.Finite ℂ E] (V : Submodule ℚ E) [FiniteDimensional ℚ V] :
    Module.finrank ℂ (Submodule.span ℂ (V : Set E)) ≤ Module.finrank ℚ V := by
  classical
  set N := Module.finrank ℚ V with hN
  let b : Fin N → E := fun i => ((Module.finBasis ℚ V) i : V)
  have hb : (V : Set E) ⊆ (Submodule.span ℂ (Set.range b) : Set E) := by
    intro x hx
    have h1 : (⟨x, hx⟩ : V) ∈ Submodule.span ℚ (Set.range (Module.finBasis ℚ V : _ → V)) := by
      rw [(Module.finBasis ℚ V).span_eq]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : x = ∑ i, ((c i : ℚ) : ℂ) • b i := by
      have h3 : x = ∑ i, (c i : ℚ) • b i := by
        have := congrArg (fun v : V => (v : E)) hc.symm
        simpa [b] using this
      rw [h3]
      exact Finset.sum_congr rfl fun i _ => (IsScalarTower.algebraMap_smul ℂ (c i) (b i)).symm
    rw [h2]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range b)) ≤ N := by
    rw [← Finsupp.range_linearCombination ℂ (v := b)]
    calc Module.finrank ℂ (Finsupp.linearCombination ℂ b).range
        ≤ Module.finrank ℂ (Fin N →₀ ℂ) := LinearMap.finrank_range_le _
      _ = N := by rw [Module.finrank_finsupp_self]; exact Fintype.card_fin N
  calc Module.finrank ℂ (Submodule.span ℂ (V : Set E))
      ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) :=
        Submodule.finrank_mono (Submodule.span_le.mpr hb)
    _ ≤ N := h1
    _ = Module.finrank ℚ V := rfl


/-- The standard basis vector of `Fin n → Option (Fin r) → ℂ`. -/
noncomputable def stdB (s : Fin n × Option (Fin r)) : Fin n → Option (Fin r) → ℂ :=
  Pi.single s.1 (Pi.single s.2 (1 : ℂ))

lemma stdB_apply (s t : Fin n × Option (Fin r)) : stdB s t.1 t.2 = if s = t then 1 else 0 := by
  rcases s with ⟨s1, s2⟩
  rcases t with ⟨t1, t2⟩
  simp only [stdB, Prod.mk.eta]
  by_cases h : s1 = t1
  · subst h
    rw [Pi.single_eq_same]
    by_cases h2 : s2 = t2
    · subst h2; simp
    · rw [Pi.single_eq_of_ne (Ne.symm h2)]; simp [h2]
  · rw [Pi.single_eq_of_ne (Ne.symm h)]; simp [h]

/-- The polynomial substitution computing the configuration at the variable `u`. -/
noncomputable def phiPoly (D : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (j : Fin r) :
    MvPolynomial (Fin n × Fin r) ℂ :=
  ∑ i : Fin n, MvPolynomial.C (D i k) * MvPolynomial.X (i, j)

lemma eval_phiPoly (D : Matrix (Fin n) (Fin n) ℂ) (u : Fin n × Fin r → ℂ)
    (k : Fin n) (j : Fin r) :
    MvPolynomial.aeval u (phiPoly D k j) = ∑ i, D i k * u (i, j) := by
  simp only [phiPoly, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  exact Finset.sum_congr rfl fun i _ => rfl


/-- Substituting `phiPoly` at the point `ubar` gives the configuration point `Q k`. -/
lemma jmat_entry (D : Matrix (Fin n) (Fin n) ℂ) (ubar : Fin n × Fin r → ℂ)
    (Q : Fin n → Fin r → ℂ) (h : ∀ k j, ∑ i, D i k * ubar (i, j) = Q k j)
    (G : MvPolynomial (Fin r) ℂ) (k : Fin n) :
    MvPolynomial.aeval ubar (MvPolynomial.aeval (fun j => phiPoly D k j) G)
      = MvPolynomial.aeval (Q k) G := by
  rw [aeval_aeval_comp ubar (fun j => phiPoly D k j) G]
  have hf : (fun j => MvPolynomial.aeval ubar (phiPoly D k j)) = Q k := by
    funext j
    rw [eval_phiPoly D ubar k j, h k j]
  rw [hf]

theorem transpose_inv_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℂ)
    (hD : D.det ≠ 0) (w : ι → ℂ) :
    (fun k => ∑ i, D i k * (Matrix.mulVec (D.transpose)⁻¹ w) i) = w := by
  have hunit : IsUnit D.transpose.det := isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose])
  have key : Matrix.mulVec (D.transpose) (Matrix.mulVec (D.transpose)⁻¹ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D.transpose hunit, Matrix.one_mulVec]
  funext k
  have h := congrFun key k
  rw [Matrix.mulVec] at h
  simpa [Matrix.transpose_apply, dotProduct] using h

/-- **The certificate determinant is nonzero.** -/
theorem jmat_det_ne_zero (Q : Fin n → Fin r → ℂ)
    (hQ : ∀ g : Fin n → (Option (Fin r) → ℂ), ∃ f : MvPolynomial (Fin r) ℂ,
      f.totalDegree ≤ d ∧ ∀ i k, MvPolynomial.aeval (Q i)
        (Option.elim k f (fun j => MvPolynomial.pderiv j f)) = g i k)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.det ≠ 0) :
    ∃ (F : (Fin n × Option (Fin r)) → MvPolynomial (Fin r) ℂ)
      (J : Matrix (Fin n × Option (Fin r)) (Fin n × Option (Fin r))
        (MvPolynomial (Fin n × Fin r) ℂ)),
      (∀ s, (F s).totalDegree ≤ d) ∧ J.det ≠ 0 ∧
      (∀ s t, J s t = MvPolynomial.aeval (fun j => phiPoly D t.1 j)
        (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s)))) := by
  classical
  have hex : ∀ s : Fin n × Option (Fin r), ∃ f : MvPolynomial (Fin r) ℂ,
      f.totalDegree ≤ d ∧ ∀ i k, MvPolynomial.aeval (Q i)
        (Option.elim k f (fun j => MvPolynomial.pderiv j f)) = stdB s i k := by
    intro s
    obtain ⟨f, hf, hfg⟩ := hQ (stdB s)
    exact ⟨f, hf, fun i k => by rw [hfg i k]⟩
  choose F hFdeg hFjet using hex
  obtain ⟨ubar, hubar⟩ : ∃ ubar : Fin n × Fin r → ℂ,
      ∀ k j, ∑ i : Fin n, D i k * ubar (i, j) = Q k j :=
    ⟨fun p => (Matrix.mulVec (D.transpose)⁻¹ (fun k => Q k p.2)) p.1,
      fun k j => congrFun (transpose_inv_mulVec D hD (fun k => Q k j)) k⟩
  set J : Matrix (Fin n × Option (Fin r)) (Fin n × Option (Fin r))
      (MvPolynomial (Fin n × Fin r) ℂ) :=
    fun s t => MvPolynomial.aeval (fun j => phiPoly D t.1 j)
      (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s))) with hJdef
  refine ⟨F, J, hFdeg, ?_, fun s t => by rw [hJdef]⟩
  -- `J` evaluated at `ubar` is the identity
  have hJmap : J.map (MvPolynomial.aeval ubar) = 1 := by
    rw [hJdef]
    ext s t
    show MvPolynomial.aeval ubar (MvPolynomial.aeval (fun j => phiPoly D t.1 j)
      (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s)))) = if s = t then 1 else 0
    rw [jmat_entry D ubar Q hubar _ t.1, hFjet s t.1 t.2, stdB_apply]
  intro hzero
  have h1 : MvPolynomial.aeval ubar J.det = (0 : ℂ) := by rw [hzero, map_zero]
  have h2 : MvPolynomial.aeval ubar J.det = (1 : ℂ) := by
    rw [show MvPolynomial.aeval ubar J.det = ((MvPolynomial.aeval ubar).mapMatrix J).det from
      AlgHom.map_det (MvPolynomial.aeval ubar) J,
      show (MvPolynomial.aeval ubar).mapMatrix J = J.map (MvPolynomial.aeval ubar) from rfl,
      hJmap, Matrix.det_one]
  rw [h2] at h1
  exact one_ne_zero h1


/-- The `ℂ`-span of the `ℚ`-polynomials inside `ℂ[x]` is everything. -/
lemma span_range_map_eq_top (r : ℕ) :
    Submodule.span ℂ (Set.range (fun g : MvPolynomial (Fin r) ℚ => g.map (algebraMap ℚ ℂ)))
      = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  rw [MvPolynomial.as_sum f]
  refine Submodule.sum_mem _ fun m _ => ?_
  have h1 : MvPolynomial.monomial m (MvPolynomial.coeff m f)
      = (MvPolynomial.coeff m f) • MvPolynomial.monomial m (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [h1]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨MvPolynomial.monomial m (1 : ℚ), ?_⟩
  show (MvPolynomial.map (algebraMap ℚ ℂ)) (MvPolynomial.monomial m (1 : ℚ))
    = MvPolynomial.monomial m (1 : ℂ)
  rw [MvPolynomial.map_monomial]
  simp

/-- Every bounded-degree complex polynomial is in the complex span of the rational
bounded-degree polynomials. -/
lemma restrictTotalDegree_subset_span_range_map (r d : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin r) ℂ d : Set (MvPolynomial (Fin r) ℂ)) ⊆
      Submodule.span ℂ (Set.range (fun g : MvPolynomial.restrictTotalDegree (Fin r) ℚ d =>
        (g.1.map (algebraMap ℚ ℂ)))) := by
  intro f hf
  have hfdeg : f.totalDegree ≤ d := (MvPolynomial.mem_restrictTotalDegree (Fin r) d f).mp hf
  rw [MvPolynomial.as_sum f]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmdeg : (m.sum fun x e => e) ≤ d := le_trans (MvPolynomial.le_totalDegree hm) hfdeg
  have h1 : MvPolynomial.monomial m (MvPolynomial.coeff m f)
      = (MvPolynomial.coeff m f) • MvPolynomial.monomial m (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [h1]
  refine Submodule.smul_mem _ _ ?_
  have hmem : (fun g : MvPolynomial.restrictTotalDegree (Fin r) ℚ d => (g.1.map (algebraMap ℚ ℂ)))
      ⟨MvPolynomial.monomial m (1 : ℚ),
        (MvPolynomial.mem_restrictTotalDegree (Fin r) d _).mpr
          (le_trans (MvPolynomial.totalDegree_monomial_le m (1 : ℚ)) hmdeg)⟩
      = MvPolynomial.monomial m (1 : ℂ) := by
    show (MvPolynomial.monomial m (1 : ℚ)).map (algebraMap ℚ ℂ)
      = MvPolynomial.monomial m (1 : ℂ)
    rw [MvPolynomial.map_monomial]
    simp
  rw [← hmem]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- The `finrank` of `Option (Fin r) → K` over `ℚ`. -/
lemma finrank_option (hn : Module.finrank ℚ K = n) :
    Module.finrank ℚ (Option (Fin r) → K) = n * (r + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hn, mul_comm, mul_left_comm]

/-- The `finrank` of `Fin n → Option (Fin r) → ℂ` over `ℂ`. -/
lemma finrank_option_complex :
    Module.finrank ℂ (Fin n → Option (Fin r) → ℂ) = n * (r + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm, mul_left_comm]

/-- The `ℂ`-jet map at the configuration is surjective when the certificate matrix is invertible. -/
lemma wpCJetBdd_surjective_of_det (D : Matrix (Fin n) (Fin n) ℂ)
    (F : (Fin n × Option (Fin r)) → MvPolynomial (Fin r) ℂ)
    (hFdeg : ∀ s, (F s).totalDegree ≤ d)
    (J : Matrix (Fin n × Option (Fin r)) (Fin n × Option (Fin r))
      (MvPolynomial (Fin n × Fin r) ℂ))
    (hJ : ∀ s t, J s t = MvPolynomial.aeval (fun j => phiPoly D t.1 j)
      (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s))))
    (u : Fin n × Fin r → ℂ) (hu : (J.map (MvPolynomial.aeval u)).det ≠ 0) :
    Function.Surjective (wpCJetBdd d (fun k j => ∑ i, D i k * u (i, j))) := by
  classical
  intro y
  set y' : Fin n × Option (Fin r) → ℂ := fun p => y p.1 p.2 with hy''
  set c : Fin n × Option (Fin r) → ℂ :=
    Matrix.mulVec (J.map (MvPolynomial.aeval u)).transpose⁻¹ y' with hc
  have hdeg : (∑ s, c s • F s).totalDegree ≤ d :=
    MvPolynomial.totalDegree_finsetSum_le
      (fun s _ => le_trans (MvPolynomial.totalDegree_smul_le (c s) (F s)) (hFdeg s))
  refine ⟨⟨∑ s, c s • F s, (MvPolynomial.mem_restrictTotalDegree (Fin r) d _).mpr hdeg⟩, ?_⟩
  rw [wpCJetBdd_apply]
  have hjet : ∀ s t, wpCJet (fun k j => ∑ i, D i k * u (i, j)) (F s) t.1 t.2
      = (J.map (MvPolynomial.aeval u)) s t := by
    intro s t
    rw [wpCJet_apply]
    show MvPolynomial.aeval (fun j => ∑ i, D i t.1 * u (i, j))
        (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s)))
      = MvPolynomial.aeval u (J s t)
    rw [hJ s t]
    exact (jmat_entry D u (fun k j => ∑ i, D i k * u (i, j)) (fun k j => rfl)
      (Option.elim t.2 (F s) (fun j => MvPolynomial.pderiv j (F s))) t.1).symm
  have hjet' : ∀ s k t, wpCJet (fun k j => ∑ i, D i k * u (i, j)) (F s) k t
      = (J.map (MvPolynomial.aeval u)) s (k, t) := by
    intro s k t
    simpa using hjet s (k, t)
  funext k t
  simp only [map_sum, map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun s _ => by rw [hjet' s k t]),
    Finset.sum_congr rfl (fun s _ => mul_comm (c s)
      ((J.map (MvPolynomial.aeval u)) s (k, t)))]
  exact congrFun (transpose_inv_mulVec (J.map (MvPolynomial.aeval u)) hu y') (k, t)

/-- If the `ℂ`-jet map at the conjugate configuration is onto, the `ℚ`-jet map at the point is
onto. -/
theorem wpJMapBdd_surjective_of_wpCJetBdd (B : Module.Basis (Fin n) ℚ K)
    (e : Fin n ≃ (K →ₐ[ℚ] ℂ)) (hn : Module.finrank ℚ K = n) (u : Fin n × Fin r → ℚ)
    (h : Function.Surjective (wpCJetBdd d (wpConf B e u))) :
    Function.Surjective (wpJMapBdd d B u) := by
  classical
  set V : Submodule ℚ (Option (Fin r) → K) := (wpJMapBdd d B u).range with hV
  set W : Submodule ℚ (Fin n → Option (Fin r) → ℂ) := V.map (wpIota e) with hW
  have hspan : Submodule.span ℂ (W : Set (Fin n → Option (Fin r) → ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, hx⟩ := h z
    let img : MvPolynomial.restrictTotalDegree (Fin r) ℚ d → MvPolynomial (Fin r) ℂ :=
      fun g => g.1.map (algebraMap ℚ ℂ)
    have hxmem : (x : MvPolynomial (Fin r) ℂ) ∈ Submodule.span ℂ (Set.range img) :=
      restrictTotalDegree_subset_span_range_map r d x.2
    have hle : Submodule.map (wpCJet (wpConf B e u)) (Submodule.span ℂ (Set.range img))
        ≤ Submodule.span ℂ (W : Set (Fin n → Option (Fin r) → ℂ)) := by
      rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      change wpCJet (wpConf B e u) (img g)
        ∈ Submodule.span ℂ (W : Set (Fin n → Option (Fin r) → ℂ))
      have hg : wpCJet (wpConf B e u) (img g) = wpIota e (wpJMapBdd d B u g) := by
        show wpCJet (wpConf B e u) (g.1.map (algebraMap ℚ ℂ))
          = wpIota e (wpJMapBdd d B u g)
        rw [wpJMapBdd_apply B u g, wpIota_wpJMap B e u g.1]
      rw [hg]
      exact Submodule.subset_span (Submodule.mem_map.mpr ⟨wpJMapBdd d B u g, ⟨g, rfl⟩, rfl⟩)
    refine hle ?_
    rw [← hx, wpCJetBdd_apply]
    exact Submodule.mem_map.mpr ⟨(x : MvPolynomial (Fin r) ℂ), hxmem, rfl⟩
  have h1 : Module.finrank ℂ (Submodule.span ℂ (W : Set (Fin n → Option (Fin r) → ℂ)))
      = n * (r + 1) := by
    rw [hspan, finrank_top]
    exact finrank_option_complex
  have h2 := finrank_span_le_finrank (Fin n → Option (Fin r) → ℂ) W
  rw [h1] at h2
  have h3 : Module.finrank ℚ W ≤ Module.finrank ℚ V := Submodule.finrank_map_le (wpIota e) V
  have h2' : n * (r + 1) ≤ Module.finrank ℚ V := le_trans h2 h3
  have h4 : Module.finrank ℚ V ≤ n * (r + 1) := by
    have hle := Submodule.finrank_le V
    rwa [finrank_option hn] at hle
  have hdim : Module.finrank ℚ V = n * (r + 1) := le_antisymm h4 h2'
  have hVtop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hdim, finrank_option hn])
  rw [← LinearMap.range_eq_top, ← hV]
  exact hVtop

/-- **Bridge lemma**: a surjective *complex* configuration of `n` points yields a rational point at
which the `ℚ`-jet map into `K^{r+1}` is surjective. -/
theorem exists_wellPoised_of_configuration (K : Type*) [Field K] [NumberField K] (n r d : ℕ)
    (hn : Module.finrank ℚ K = n) (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
    (hd : 0 < d)
    (hconf : ∃ Q : Fin n → (Fin r → ℂ), ∀ g : Fin n → (Option (Fin r) → ℂ),
      ∃ f : MvPolynomial (Fin r) ℂ, f.totalDegree ≤ d ∧
        ∀ i k, MvPolynomial.eval (Q i) (Option.elim k f (fun j => MvPolynomial.pderiv j f)) = g i k) :
    ∃ u : Fin n × Fin r → ℚ, ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ,
      f.totalDegree ≤ d ∧
      MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) f = g.1 ∧
      ∀ j : Fin r, MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) (MvPolynomial.pderiv j f) = g.2 j := by
  classical
  have _ : 0 < d := hd
  obtain ⟨B, hB⟩ := Commons.NumberTheory.NumberField.exists_basis_coe_ringOfIntegers K ωb hn
  obtain ⟨Q, hQ⟩ := hconf
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = n := by
    rw [Commons.NumberTheory.NumberField.card_algHom_eq_finrank]
    exact hn
  let e : Fin n ≃ (K →ₐ[ℚ] ℂ) := (Fintype.equivFinOfCardEq hcard).symm
  let D : Matrix (Fin n) (Fin n) ℂ := fun i k => (e k) (B i)
  have hDdet : D.det ≠ 0 := by
    have h := embeddingsMatrixReindex_det_ne_zero K B e
    rw [show Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => B i) e = D from by
      ext i k
      simp [D, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]] at h
    exact h
  obtain ⟨F, J, hFdeg, hJdet, hJ⟩ := jmat_det_ne_zero (d := d) Q hQ D hDdet
  obtain ⟨u, hu⟩ := exists_rat_eval_ne_zero' J.det hJdet
  have hu' : (J.map (MvPolynomial.aeval (fun p => ((u p : ℚ) : ℂ)))).det ≠ 0 := by
    have hkey : (J.map (MvPolynomial.aeval (fun p => ((u p : ℚ) : ℂ)))).det
        = MvPolynomial.eval (fun p => ((u p : ℚ) : ℂ)) J.det := by
      rw [show (J.map (MvPolynomial.aeval (fun p => ((u p : ℚ) : ℂ))))
            = ((MvPolynomial.aeval (fun p => ((u p : ℚ) : ℂ))).mapMatrix J) from by
          rw [AlgHom.mapMatrix_apply],
        ← AlgHom.map_det, MvPolynomial.aeval_eq_eval]
    rw [hkey]
    exact hu
  have hsurjC : Function.Surjective
      (wpCJetBdd d (fun k j => ∑ i, D i k * ((u (i, j) : ℚ) : ℂ))) :=
    wpCJetBdd_surjective_of_det D F hFdeg J hJ (fun p => ((u p : ℚ) : ℂ)) hu'
  have hconf_eq : wpConf B e u = fun k j => ∑ i, D i k * ((u (i, j) : ℚ) : ℂ) := by
    funext k j
    simp only [wpConf, D]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsurjC' : Function.Surjective (wpCJetBdd d (wpConf B e u)) := by
    rw [hconf_eq]
    exact hsurjC
  have hsurjK : Function.Surjective (wpJMapBdd d B u) :=
    wpJMapBdd_surjective_of_wpCJetBdd B e hn u hsurjC'
  have hpt : wpPt B u
      = fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) •
          (((ωb i : NumberField.RingOfIntegers K) : K)) := by
    funext j
    simp only [wpPt]
    exact Finset.sum_congr rfl fun i _ => by rw [hB i]
  refine ⟨u, fun g => ?_⟩
  obtain ⟨f, hf⟩ := hsurjK (fun t : Option (Fin r) => Option.elim t g.1 g.2)
  refine ⟨f.1, (MvPolynomial.mem_restrictTotalDegree (Fin r) d f.1).mp f.2, ?_, ?_⟩
  · have hthis : MvPolynomial.aeval (wpPt B u) f.1 = g.1 := by
      have h := congr_fun hf none
      rw [wpJMapBdd_apply, wpJMap_apply, Option.elim_none] at h
      exact h
    rw [hpt] at hthis
    exact hthis
  · intro j
    have hthis : MvPolynomial.aeval (wpPt B u) (MvPolynomial.pderiv j f.1) = g.2 j := by
      have h := congr_fun hf (some j)
      rw [wpJMapBdd_apply, wpJMap_apply, Option.elim_some] at h
      exact h
    rw [hpt] at hthis
    exact hthis

/-- Well-poised points exist: for a number field `K` of degree `n` and integers `r, d` with
`0 < d` and `(n-1)(r+1) < (d+r-1).choose r`, there is a point of `K^r` (with coordinates given in a
`ℤ`-basis `ωb` of `𝓞 K`) at which every value-and-gradient pair in `K × K^r` is realised by a
polynomial of total degree `≤ d` with rational coefficients. -/
theorem exists_wellPoised_point (K : Type*) [Field K] [NumberField K] (n r d : ℕ)
    (hn : Module.finrank ℚ K = n) (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
    (hd : 0 < d) (h : (n - 1) * (r + 1) < (d + r - 1).choose r) :
    ∃ u : Fin n × Fin r → ℚ, ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ,
      f.totalDegree ≤ d ∧
      MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) f = g.1 ∧
      ∀ j : Fin r, MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) (MvPolynomial.pderiv j f) = g.2 j := by
  obtain ⟨Q, hQ⟩ := Commons.Algebra.MvPolynomial.exists_points_eval_surjective r d n ℂ h
  exact exists_wellPoised_of_configuration K n r d hn ωb hd ⟨Q, hQ⟩

end Commons.NumberTheory.NumberField