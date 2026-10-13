import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.DZA.gf_degzero_away
import Submission.Work.DSCOH.degZero_exact
import Submission.Work.DSCOH.degZero_locMapOf
import Submission.Work.DSCOH.degZero_exists_repr
import Submission.Work.DSCOH.resAt_degZero

/-!
# Vocabulary for `Work.DSEQP.Term.degZero_quot_away`

The degree-zero part `(M[1/x_S])₀ = Work.DSCOH.degZero (Mg i) S` of the chart localisation of
`M = A[x₀,…,x_N] ⧸ J` (`J = Work.DSEQP.Jvan i` the vanishing ideal of the closed subscheme
`i : X ↪ ℙᴺ_A`) is the quotient `Away 𝒜 (x_S) ⧸ Work.DSEQP.chartJ i S` of the chart ring by the
chart ideal of `J`.

The bridge is the exactness of the degree-zero part of the chart localisation applied to the
sequence

`0 → J → R → R ⧸ J → 0`

(`Work.DSCOH.degZero_exact`): the vanishing ideal is regarded as the graded module whose `d`-th
piece is `J ∩ 𝒜_d` (`Jgr` below), and the localisation of the quotient map `R → R ⧸ J` restricts
to a surjection `psi S : (R[1/x_S])₀ → (M[1/x_S])₀` whose kernel is the image of
`kappa S : (J[1/x_S])₀ → (R[1/x_S])₀` (`Img S` below).  Composing with the identification
`Work.DSEQP.DZA.toAway : (R[1/x_S])₀ ≅ Away 𝒜 (x_S)` of `Work.DSEQP.DZA.gf_degzero_away` turns the
kernel into `chartJ i S`.
-/

namespace Work.DSEQP.Term

open MvPolynomial

universe a u v w

variable {A : Type a} [CommRing A] {N : ℕ}
variable {X : AlgebraicGeometry.Scheme.{a}}

noncomputable section

/-! ## The vanishing ideal as a graded module -/

/-- The graded pieces `J ∩ 𝒜_d` of the vanishing ideal `J = Jvan i`, regarded as a submodule of
`J` (i.e. of the module `↥J`), so that `Work.DSCOH.degZero` applies to the graded module `J`. -/
noncomputable def Jgr (i : X ⟶ DSMap.PSpace A N) (d : ℕ) : Submodule A ↥(Work.DSEQP.Jvan i) :=
  Submodule.comap ((Submodule.subtype (Work.DSEQP.Jvan i)).restrictScalars A)
    (Work.DSCOH.homSub A (N + 1) d)

@[simp] lemma mem_Jgr {i : X ⟶ DSMap.PSpace A N} {d : ℕ} {f : ↥(Work.DSEQP.Jvan i)} :
    f ∈ Jgr (A := A) (N := N) i d ↔
      (f : MvPolynomial (Fin (N + 1)) A) ∈ Work.DSCOH.homSub A (N + 1) d :=
  Iff.rfl

/-- `J = ⨁_d (J ∩ 𝒜_d)` is a graded submodule of `R`. -/
instance Jgr_gradedSMul (i : X ⟶ DSMap.PSpace A N) :
    SetLike.GradedSMul (DSMap.PGr A N) (Jgr (A := A) (N := N) i) where
  smul_mem d e a x ha hx := by
    rw [Jgr, Submodule.mem_comap] at hx ⊢
    show ((a • x : ↥(Work.DSEQP.Jvan i)) : MvPolynomial (Fin (N + 1)) A) ∈
      Work.DSCOH.homSub A (N + 1) (d + e)
    rw [Submodule.coe_smul]
    exact SetLike.mul_mem_graded ha hx

/-! ## The maps `psi` and `kappa` on the degree-zero parts -/

variable (i : X ⟶ DSMap.PSpace A N)

/-- The map `(R[1/x_S])₀ → (M[1/x_S])₀` induced by the quotient map `R → M = R ⧸ J`. -/
noncomputable def psi (S : Finset (Fin (N + 1))) :
    ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
        (Work.DSCOH.homSub A (N + 1)) S) →ₗ[A]
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S) :=
  Work.DSCOH.degZeroMapOf (Work.DSCOH.homSub A (N + 1)) (Work.DSEQP.Mg i)
    (Submodule.mkQ (Work.DSEQP.Jvan i)) S
    (Work.DSCOH.degZero_locMapOf (Work.DSCOH.homSub A (N + 1)) (Work.DSEQP.Mg i)
      (Submodule.mkQ (Work.DSEQP.Jvan i)) (fun d => le_of_eq rfl) S)

lemma psi_apply (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    (psi i S x).1 = Work.DSCOH.locMapOf (A := A) (n := N + 1)
      (Submodule.mkQ (Work.DSEQP.Jvan i)) S x.1 :=
  rfl

/-- The map `(J[1/x_S])₀ → (R[1/x_S])₀` induced by the inclusion `J ↪ R`. -/
noncomputable def kappa (S : Finset (Fin (N + 1))) :
    ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
        (Jgr (A := A) (N := N) i) S) →ₗ[A]
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
        (Work.DSCOH.homSub A (N + 1)) S) :=
  Work.DSCOH.degZeroMapOf (Jgr (A := A) (N := N) i) (Work.DSCOH.homSub A (N + 1))
    (Submodule.subtype (Work.DSEQP.Jvan i)) S
    (Work.DSCOH.degZero_locMapOf (Jgr (A := A) (N := N) i) (Work.DSCOH.homSub A (N + 1))
      (Submodule.subtype (Work.DSEQP.Jvan i))
      (fun d => by
        rintro y ⟨x, hx, rfl⟩
        exact mem_Jgr.mp hx) S)

lemma kappa_apply (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
      (Jgr (A := A) (N := N) i) S)) :
    (kappa i S x).1 = Work.DSCOH.locMapOf (A := A) (n := N + 1)
      (Submodule.subtype (Work.DSEQP.Jvan i)) S x.1 :=
  rfl

/-- The kernel of `psi S`, as a submodule of `(R[1/x_S])₀`: the image of `(J[1/x_S])₀`. -/
noncomputable def Img (S : Finset (Fin (N + 1))) :
    Submodule A ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S) :=
  Submodule.map (kappa (A := A) (N := N) i S) ⊤

/-- The canonical element `kappa S x` of `Img S`. -/
lemma kappa_mem_Img (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
      (Jgr (A := A) (N := N) i) S)) :
    kappa (A := A) (N := N) i S x ∈ Img (A := A) (N := N) i S := by
  rw [Img, Submodule.mem_map]
  exact ⟨x, Submodule.mem_top, rfl⟩

/-- An element of `Img S` is the image of some element of `(J[1/x_S])₀`. -/
lemma mem_Img {S : Finset (Fin (N + 1))}
    {y : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)} (h : y ∈ Img (A := A) (N := N) i S) :
    ∃ x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
        (Jgr (A := A) (N := N) i) S), kappa (A := A) (N := N) i S x = y := by
  rw [Img, Submodule.mem_map] at h
  exact ⟨h.choose, h.choose_spec.2⟩

/-! ## Exactness of `0 → (J[1/x_S])₀ → (R[1/x_S])₀ → (M[1/x_S])₀ → 0` -/

/-- The degree-zero part of the chart localisation of `0 → J → R → R ⧸ J → 0` is right exact. -/
theorem degZero_exact_J (S : Finset (Fin (N + 1))) :
    (∀ z ∈ Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S,
      ∃ y ∈ Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
          (Work.DSCOH.homSub A (N + 1)) S,
        Work.DSCOH.locMapOf (A := A) (n := N + 1) (Submodule.mkQ (Work.DSEQP.Jvan i)) S y = z) ∧
    (∀ y ∈ Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
          (Work.DSCOH.homSub A (N + 1)) S,
        Work.DSCOH.locMapOf (A := A) (n := N + 1) (Submodule.mkQ (Work.DSEQP.Jvan i)) S y = 0 →
      ∃ x ∈ Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
          (Jgr (A := A) (N := N) i) S,
        Work.DSCOH.locMapOf (A := A) (n := N + 1)
          (Submodule.subtype (Work.DSEQP.Jvan i)) S x = y) := by
  have hker : ∀ d : ℕ,
      Work.DSCOH.homSub A (N + 1) d ⊓ (LinearMap.ker
        (((Submodule.mkQ (Work.DSEQP.Jvan i)).restrictScalars A))) ≤
        Submodule.map (((Submodule.subtype (Work.DSEQP.Jvan i)).restrictScalars A))
          (Jgr (A := A) (N := N) i d) := by
    intro d y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply] at hy2
    have hyJ : y ∈ Work.DSEQP.Jvan i := by
      have hy2' : y ∈ LinearMap.ker (Submodule.mkQ (Work.DSEQP.Jvan i)) := hy2
      rwa [Submodule.ker_mkQ] at hy2'
    exact Submodule.mem_map.mpr ⟨⟨y, hyJ⟩, mem_Jgr.mpr hy1, rfl⟩
  have h := Work.DSCOH.degZero_exact (A := A) (n := N + 1)
    (M := ↥(Work.DSEQP.Jvan i)) (M' := MvPolynomial (Fin (N + 1)) A)
    (M'' := Work.DSEQP.Mmod i)
    (ℳ := Jgr (A := A) (N := N) i) (ℳ' := Work.DSCOH.homSub A (N + 1))
    (ℳ'' := Work.DSEQP.Mg i)
    (Submodule.subtype (Work.DSEQP.Jvan i)) (Submodule.mkQ (Work.DSEQP.Jvan i))
    (Submodule.subtype_injective (Work.DSEQP.Jvan i))
    (fun d => by
      rintro y ⟨x, hx, rfl⟩
      exact mem_Jgr.mp hx)
    (fun d => rfl) hker S
  exact ⟨h.2.2.2.2, h.2.2.2.1⟩

/-- `psi S` is surjective. -/
lemma psi_surjective (S : Finset (Fin (N + 1))) : Function.Surjective (psi (A := A) (N := N) i S) := by
  intro z
  obtain ⟨y, hy, hyz⟩ := (degZero_exact_J (A := A) (N := N) i S).1 z z.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩


/-- The map induced by `φ` on the chart localisations sends `m / x_S^k` to `φ m / x_S^k`. -/
lemma locMapOf_divPow_toLoc' {M : Type u} [AddCommGroup M] [Module A M]
    [Module (Work.DSCOH.Poly A (N + 1)) M] [IsScalarTower A (Work.DSCOH.Poly A (N + 1)) M]
    {M' : Type v} [AddCommGroup M'] [Module A M']
    [Module (Work.DSCOH.Poly A (N + 1)) M'] [IsScalarTower A (Work.DSCOH.Poly A (N + 1)) M']
    (φ : M →ₗ[Work.DSCOH.Poly A (N + 1)] M') (S : Finset (Fin (N + 1))) (k : ℕ) (m : M) :
    Work.DSCOH.locMapOf (A := A) (M := M) φ S
        (Work.DSCOH.divPow (A := A) (M := M) S k (Work.DSCOH.toLoc (A := A) (M := M) S m)) =
      Work.DSCOH.divPow (A := A) (M := M') S k
        (Work.DSCOH.toLoc (A := A) (M := M') S (φ m)) := by
  simp only [Work.DSCOH.locMapOf, Work.DSCOH.divPow, Work.DSCOH.toLoc,
    LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]
  rw [IsLocalizedModule.map_LocalizedModules]


/-- The chart ideal `chartJ i S`, regarded as an `A`-submodule of the chart ring (its carrier is
the same set; only the scalar ring changes, from the chart ring to `A`). -/
noncomputable def chartJA (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    Submodule A (HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) where
  carrier := (Work.DSEQP.chartJ i S : Set _)
  zero_mem' := (Work.DSEQP.chartJ i S).zero_mem
  add_mem' := fun hx hy => (Work.DSEQP.chartJ i S).add_mem hx hy
  smul_mem' := fun r x hx =>
    Ideal.mul_mem_left _ ((algebraMap A (HomogeneousLocalization.Away (DSMap.PGr A N)
      (Work.DSEQP.xS (A := A) S))) r) hx

@[simp] lemma mem_chartJA {i : X ⟶ DSMap.PSpace A N} {S : Finset (Fin (N + 1))}
    {z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)} :
    z ∈ chartJA (A := A) (N := N) i S ↔ z ∈ Work.DSEQP.chartJ i S := Iff.rfl

/-! ## Functoriality of the chart localisation -/

/-- Chart localisation is functorial: it sends a composite of linear maps to the composite of the
induced maps. -/
lemma locMapOf_comp {M : Type u} [AddCommGroup M] [Module A M]
    [Module (Work.DSCOH.Poly A (N + 1)) M] [IsScalarTower A (Work.DSCOH.Poly A (N + 1)) M]
    {M' : Type v} [AddCommGroup M'] [Module A M']
    [Module (Work.DSCOH.Poly A (N + 1)) M'] [IsScalarTower A (Work.DSCOH.Poly A (N + 1)) M']
    {M'' : Type w} [AddCommGroup M''] [Module A M'']
    [Module (Work.DSCOH.Poly A (N + 1)) M''] [IsScalarTower A (Work.DSCOH.Poly A (N + 1)) M'']
    (φ : M →ₗ[Work.DSCOH.Poly A (N + 1)] M') (ψ : M' →ₗ[Work.DSCOH.Poly A (N + 1)] M'')
    (S : Finset (Fin (N + 1))) :
    Work.DSCOH.locMapOf (A := A) (M := M) (ψ.comp φ) S =
      (Work.DSCOH.locMapOf (A := A) (M := M') ψ S).comp
        (Work.DSCOH.locMapOf (A := A) (M := M) φ S) := by
  unfold Work.DSCOH.locMapOf
  exact IsLocalizedModule.map_comp' (S := Work.DSCOH.subS (A := A) (n := N + 1) S) _ _ _ φ ψ

/-- The composite `psi S ∘ kappa S` is zero. -/
lemma psi_kappa (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := ↥(Work.DSEQP.Jvan i))
      (Jgr (A := A) (N := N) i) S)) :
    psi (A := A) (N := N) i S (kappa (A := A) (N := N) i S x) = 0 := by
  apply Subtype.ext
  show Work.DSCOH.locMapOf (A := A) (n := N + 1) (Submodule.mkQ (Work.DSEQP.Jvan i)) S
      (Work.DSCOH.locMapOf (A := A) (n := N + 1)
        (Submodule.subtype (Work.DSEQP.Jvan i)) S x.1) = 0
  have h0 : (Submodule.mkQ (Work.DSEQP.Jvan i)).comp
      (Submodule.subtype (Work.DSEQP.Jvan i)) = 0 := by
    rw [← LinearMap.range_le_ker_iff, Submodule.range_subtype, Submodule.ker_mkQ]
  rw [← LinearMap.comp_apply, ← locMapOf_comp (A := A) (N := N), h0]
  simp [Work.DSCOH.locMapOf]

/-- The kernel of `psi S` is the image of `kappa S`. -/
lemma ker_psi (S : Finset (Fin (N + 1))) :
    LinearMap.ker (psi (A := A) (N := N) i S) = Img (A := A) (N := N) i S := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : Work.DSCOH.locMapOf (A := A) (n := N + 1)
        (Submodule.mkQ (Work.DSEQP.Jvan i)) S y.1 = 0 := by
      simpa [psi_apply] using congrArg Subtype.val hy
    obtain ⟨x, hx, hxy⟩ := (degZero_exact_J (A := A) (N := N) i S).2 y y.2 hy0
    have hk : kappa (A := A) (N := N) i S ⟨x, hx⟩ = y := Subtype.ext hxy
    rw [← hk]
    exact kappa_mem_Img (A := A) (N := N) i S ⟨x, hx⟩
  · intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, rfl⟩ := mem_Img (A := A) (N := N) i hy
    exact psi_kappa (A := A) (N := N) i S x

end

end Work.DSEQP.Term
