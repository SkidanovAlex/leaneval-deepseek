import Mathlib
import Submission.Work.Mostow.Margulis.ComplexifyOrth
import Submission.Work.Mostow.Margulis.cActHom_isSemisimple

namespace Work.Mostow

open Module.End

/-!
# Counting a commuting family of linear isometries by its eigenvalues

Let `V` be a finite-dimensional real inner product space and let `A` be a finite pairwise
commuting family of linear isometries of `V`.  Writing `cAct` for the complexification
`V × V` of `V` (`Submission/Work/Mostow/Margulis/ComplexifyOrth.lean`), every `a ∈ A` is
semisimple on `V × V` (`cActHom_isSemisimple`), so the family is simultaneously
diagonalizable over `ℂ`: the space is the direct sum of the *joint* eigenspaces
`⨅ a, eigenspace (cAct a) (χ a)`, indexed by functions `χ : A → ℂ`.

Every such joint eigenspace is a nonzero subspace of the `n`-dimensional complex space
`V × V`, and any two distinct ones are independent whenever the corresponding joint
eigenvalues differ, so there are at most `n = finrank ℂ (V × V)` of them.  Each element
`a ∈ A` is determined by the family of scalars by which it acts on these joint eigenspaces;
if all those scalars lie in a finite set `S`, then `A` injects into the set of functions from
the (at most `n`) joint eigenspaces to `S`, giving `A.card ≤ S.card ^ n ≤ (S.card + 1) ^ (2n+1)`.

This is the counting lemma `Work.Mostow.conjCountCard`.
-/

/-- The coercion from `M ≃ₗ[𝕜] M` to `M →ₗ[𝕜] M` is a monoid homomorphism. -/
lemma conjCount_linEquiv_coe_mul {𝕜 M : Type*} [Semiring 𝕜] [AddCommMonoid M] [Module 𝕜 M]
    (e₁ e₂ : M ≃ₗ[𝕜] M) :
    ((↑(e₁ * e₂) : M →ₗ[𝕜] M)) = (↑e₁ : M →ₗ[𝕜] M) * (↑e₂ : M →ₗ[𝕜] M) := by
  ext x
  simp [Module.End.mul_apply]

/-- A pairwise commuting family of real linear isometries stays pairwise commuting after
complexification. -/
lemma conjCount_cActHom_pairwise_commute {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : Finset (V ≃ₗᵢ[ℝ] V)) (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) :
    Pairwise fun i j : ↥A => Commute
      ((Work.Mostow.Margulis.cAct (i : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V)))
      ((Work.Mostow.Margulis.cAct (j : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V))) := by
  intro i j _
  have h2 : (Work.Mostow.Margulis.cActHom (i : V ≃ₗᵢ[ℝ] V) *
        Work.Mostow.Margulis.cActHom (j : V ≃ₗᵢ[ℝ] V) : (V × V) ≃ₗ[ℂ] (V × V)) =
      (Work.Mostow.Margulis.cActHom (j : V ≃ₗᵢ[ℝ] V) *
        Work.Mostow.Margulis.cActHom (i : V ≃ₗᵢ[ℝ] V) : (V × V) ≃ₗ[ℂ] (V × V)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (hcomm i i.2 j j.2)
  show (Work.Mostow.Margulis.cAct (i : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V)) *
      (Work.Mostow.Margulis.cAct (j : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V)) =
    (Work.Mostow.Margulis.cAct (j : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V)) *
      (Work.Mostow.Margulis.cAct (i : V ≃ₗᵢ[ℝ] V) : (V × V) →ₗ[ℂ] (V × V))
  rw [← conjCount_linEquiv_coe_mul, ← conjCount_linEquiv_coe_mul]
  exact congrArg (fun e : (V × V) ≃ₗ[ℂ] (V × V) => (e : (V × V) →ₗ[ℂ] (V × V))) h2

/-- The joint eigenspaces of a pairwise commuting family of semisimple endomorphisms of a
finite-dimensional vector space over an algebraically closed field span the whole space. -/
lemma conjCount_iSup_iInf_eigenspace_eq_top {K V ι : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j => Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple) :
    ⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i) = ⊤ := by
  have h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := fun i =>
    (hss i).isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff.mpr (hss i).iSup_eigenspace_eq_top
  have key :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f hcomm h'
  have hkey : (⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i))
      = (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) :=
    iSup_congr fun χ => iInf_congr fun i =>
      Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace ((hss i).isFinitelySemisimple) (χ i)
  rw [hkey] at key; exact key

/-- The joint eigenspaces of a pairwise commuting family of semisimple endomorphisms are
independent. -/
lemma conjCount_iSupIndep_iInf_eigenspace {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : ι → Module.End K V) (hcomm : Pairwise fun i j => Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple) :
    iSupIndep fun χ : ι → K => ⨅ i, (f i).eigenspace (χ i) := by
  have hcomm' : ∀ i j, Commute (f i) (f j) := by
    intro i j
    by_cases h : i = j
    · subst h; exact Commute.refl _
    · exact hcomm h
  have hmaps : ∀ i j (φ : K),
      Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (f := f j) (g := f i) (hcomm' j i) φ
  have key := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have hkey : (fun χ : ι → K => ⨅ i, (f i).maxGenEigenspace (χ i))
      = (fun χ : ι → K => ⨅ i, (f i).eigenspace (χ i)) :=
    funext fun χ => iInf_congr fun i =>
      Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace ((hss i).isFinitelySemisimple) (χ i)
  rwa [hkey] at key

/-- The complexification of `EuclideanSpace ℝ (Fin n)` has complex dimension `n`. -/
lemma conjCount_finrank_complex_prod (n : ℕ) :
    Module.finrank ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) = n := by
  have h1 : Module.finrank ℝ ℂ * Module.finrank ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    Module.finrank_mul_finrank ℝ ℂ _
  simp only [Complex.finrank_real_complex, Module.finrank_prod, finrank_euclideanSpace,
    Fintype.card_fin] at h1
  omega

/-- Counting lemma: a finite pairwise commuting family of linear isometries of `E n` whose
complex eigenvalues all lie in a fixed finite set `S` has at most `(S.card + 1)^(2n+1)`
elements. -/
theorem conjCountCard (n : ℕ) (S : Finset ℂ) (A : Finset (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)))
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hspec : ∀ a ∈ A, ∀ μ : ℂ,
      Module.End.HasEigenvalue
        ((Work.Mostow.Margulis.cAct a : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℂ] (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))) μ → μ ∈ S) :
    A.card ≤ (S.card + 1) ^ (2 * n + 1) := by
  classical
  let f : ↥A → Module.End ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun a => (Work.Mostow.Margulis.cAct (a : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℂ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  have hcommf : Pairwise fun i j => Commute (f i) (f j) := conjCount_cActHom_pairwise_commute A hcomm
  have hss : ∀ i, (f i).IsSemisimple := fun i =>
    Work.Mostow.Margulis.cActHom_isSemisimple
      (i : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
  let W : (↥A → ℂ) → Submodule ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun χ => ⨅ i, (f i).eigenspace (χ i)
  have hspan : ⨆ χ : ↥A → ℂ, W χ = ⊤ :=
    conjCount_iSup_iInf_eigenspace_eq_top f hcommf hss
  have hindep : iSupIndep W := conjCount_iSupIndep_iInf_eigenspace f hcommf hss
  -- the joint eigenspaces, restricted to the nontrivial ones, still span
  have hspan' : (⨆ χ : {χ : ↥A → ℂ // W χ ≠ ⊥}, W χ.1) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun χ => ?_
    by_cases hχ : W χ = ⊥
    · rw [hχ]; exact bot_le
    · exact le_iSup (fun χ : {χ : ↥A → ℂ // W χ ≠ ⊥} => W χ.1) ⟨χ, hχ⟩
  haveI : Fintype {χ : ↥A → ℂ // W χ ≠ ⊥} := hindep.fintypeNeBotOfFiniteDimensional
  -- there are at most `finrank ℂ (V × V) = n` of them
  have hcard : Fintype.card {χ : ↥A → ℂ // W χ ≠ ⊥} ≤ n := by
    have h := hindep.subtype_ne_bot_le_finrank
      (R := ℂ) (M := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    rwa [conjCount_finrank_complex_prod n] at h
  have hspec' : ∀ a : ↥A, ∀ μ : ℂ, Module.End.HasEigenvalue (f a) μ → μ ∈ S := by
    intro a μ hμ
    exact hspec a a.2 μ hμ
  -- each member of `A` is determined by the eigenvalues it assigns to the joint eigenspaces
  let Φ : ↥A → ({χ : ↥A → ℂ // W χ ≠ ⊥} → S) := fun a χ =>
    ⟨χ.1 a, hspec' a (χ.1 a) (by
      rw [Module.End.hasEigenvalue_iff]
      intro hbot
      have hle : W χ.1 ≤ (f a).eigenspace (χ.1 a) :=
        iInf_le (fun i => (f i).eigenspace (χ.1 i)) a
      rw [hbot] at hle
      exact χ.2 (le_bot_iff.mp hle))⟩
  have hinj : Function.Injective Φ := by
    intro a a' h
    have hval : ∀ χ : {χ : ↥A → ℂ // W χ ≠ ⊥}, χ.1 a = χ.1 a' := fun χ =>
      congrArg Subtype.val (congrFun h χ)
    have hle : ∀ χ : {χ : ↥A → ℂ // W χ ≠ ⊥}, W χ.1 ≤ LinearMap.ker (f a - f a') := by
      intro χ v hv
      rw [LinearMap.mem_ker]
      have hv1 : v ∈ (f a).eigenspace (χ.1 a) :=
        (Submodule.mem_iInf (fun i => (f i).eigenspace (χ.1 i))).mp hv a
      have hv2 : v ∈ (f a').eigenspace (χ.1 a') :=
        (Submodule.mem_iInf (fun i => (f i).eigenspace (χ.1 i))).mp hv a'
      rw [Module.End.mem_eigenspace_iff] at hv1 hv2
      rw [LinearMap.sub_apply, hv1, hv2, hval χ, sub_self]
    have hzero : f a - f a' = 0 := by
      have htop : (⊤ : Submodule ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
          ≤ LinearMap.ker (f a - f a') := by
        rw [← hspan']; exact iSup_le hle
      exact LinearMap.ker_eq_top.mp (top_le_iff.mp htop)
    have hf : f a = f a' := sub_eq_zero.mp hzero
    have hiso : (a : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) =
        (a' : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) := by
      refine LinearIsometryEquiv.ext fun u => ?_
      have hcong := congrArg
        (fun g : Module.End ℂ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          g (u, 0)) hf
      have h1 : (Work.Mostow.Margulis.cAct (a : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] _) (u, 0)) =
          (Work.Mostow.Margulis.cAct (a' : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] _) (u, 0)) := hcong
      simp only [Work.Mostow.Margulis.cAct_apply, map_zero, Prod.mk.injEq] at h1
      exact h1.1
    exact Subtype.ext hiso
  have hcard_inj : Fintype.card ↥A ≤ S.card ^ Fintype.card {χ : ↥A → ℂ // W χ ≠ ⊥} := by
    have h := Fintype.card_le_of_injective Φ hinj
    simp only [Fintype.card_fun, Fintype.card_coe] at h ⊢
    exact h
  calc A.card = Fintype.card ↥A := (Fintype.card_coe A).symm
    _ ≤ S.card ^ Fintype.card {χ : ↥A → ℂ // W χ ≠ ⊥} := hcard_inj
    _ ≤ (S.card + 1) ^ Fintype.card {χ : ↥A → ℂ // W χ ≠ ⊥} :=
        Nat.pow_le_pow_left (Nat.le_succ _) _
    _ ≤ (S.card + 1) ^ (2 * n + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)

end Work.Mostow
