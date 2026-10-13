import Mathlib
import Submission.Work.DSFFP.Defs
import Submission.Work.DSFFP.tpure_of_coker_quot
import Submission.Work.DSFFP.tpure_of_flat_quot_top
import Submission.Work.DSFFP.tpure_of_iSup

/-!
# Step A of the local flatness criterion (Stacks 10.99.8, tag 051C)

Deliverable: `Work.DSFFP.tpure_of_smul_top_le`.  The proof is assembled from the three
ingredients established elsewhere in this directory,

* `Work.DSFFP.tpure_of_coker_quot`     (cokernel equal to `S ⧸ I`),
* `Work.DSFFP.tpure_of_flat_quot_top`  (both modules killed by `I`),
* `Work.DSFFP.tpure_of_iSup`           (tensor products commute with filtered unions),

together with (i) the "finitely generated cokernel" case (`injective_rTensor_ker_fin`),
(ii) an abstract diagram chase (`injective_rTensor_of_chase`) and
(iii) the fibre product of two maps with a common codomain.
-/

open TensorProduct

set_option maxHeartbeats 4000000

namespace Work.DSFFP

universe u

variable {S : Type u} [CommRing S]

/-! ## Two elementary auxiliary facts -/

/-- The identity is `T`-pure. -/
theorem injective_rTensor_id {T M : Type u} [AddCommGroup T] [Module S T] [AddCommGroup M]
    [Module S M] : Function.Injective (LinearMap.rTensor T (LinearMap.id : M →ₗ[S] M)) := by
  rw [LinearMap.rTensor_id]
  exact Function.injective_id

/-- The inclusion `⊤ ⊆ M` is `T`-pure: it is split by `Submodule.topEquiv`. -/
theorem injective_rTensor_subtype_top {T M : Type u} [AddCommGroup T] [Module S T]
    [AddCommGroup M] [Module S M] :
    Function.Injective (LinearMap.rTensor T (Submodule.subtype (⊤ : Submodule S M))) := by
  refine TPure.of_retract (T := T)
    (r := (Submodule.topEquiv (R := S) (M := M)).symm.toLinearMap) ?_
  ext x
  rfl

/-- Tensoring a linear equivalence with `id_T` is injective. -/
theorem injective_rTensor_linearEquiv {T M N : Type u} [AddCommGroup T] [Module S T]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    Function.Injective (LinearMap.rTensor T (e : M →ₗ[S] N)) :=
  TPure.of_retract (T := T) (r := (e.symm : N →ₗ[S] M))
    (LinearMap.ext fun x => e.symm_apply_apply x)

/-- Tensoring a linear equivalence with `id_T` is surjective. -/
theorem surjective_rTensor_linearEquiv {T M N : Type u} [AddCommGroup T] [Module S T]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    Function.Surjective (LinearMap.rTensor T (e : M →ₗ[S] N)) := by
  intro y
  refine ⟨LinearMap.rTensor T ((e.symm : N →ₗ[S] M)) y, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    show ((e : M →ₗ[S] N).comp (e.symm : N →ₗ[S] M)) = LinearMap.id from
      LinearMap.ext fun x => e.apply_symm_apply x, LinearMap.rTensor_id]
  rfl

/-- If `A ≤ B`, the two inclusions `Submodule.inclusion h : ↥A → ↥B` and
`Submodule.subtype (A.comap B.subtype) : ↥(A.comap B.subtype) → ↥B` are intertwined by the
canonical linear equivalence `A ≃ₗ A.comap B.subtype`.  Consequently injectivity after `⊗[S] T`
is the same for both. -/
theorem rTensor_inclusion_iff_rTensor_comap {T : Type u} [AddCommGroup T] [Module S T]
    {Q : Type u} [AddCommGroup Q] [Module S Q] {A B : Submodule S Q} (h : A ≤ B) :
    Function.Injective (LinearMap.rTensor T (Submodule.inclusion h)) ↔
      Function.Injective (LinearMap.rTensor T (Submodule.subtype (A.comap B.subtype))) := by
  let e : A ≃ₗ[S] (A.comap B.subtype) :=
    { toFun := fun x => ⟨⟨(x : Q), h x.2⟩, x.2⟩
      invFun := fun y => ⟨(y.1 : Q), y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext <;> rfl
      map_add' := fun x y => by ext <;> rfl
      map_smul' := fun c x => by ext <;> rfl }
  have he1 : (Submodule.inclusion h) =
      (Submodule.subtype (A.comap B.subtype)).comp (e : A →ₗ[S] _) := by
    ext x
    rfl
  have he2 : (Submodule.subtype (A.comap B.subtype)) =
      (Submodule.inclusion h).comp (e.symm : (A.comap B.subtype) →ₗ[S] A) := by
    ext x
    rfl
  constructor
  · intro hh
    rw [he2, LinearMap.rTensor_comp]
    exact hh.comp (injective_rTensor_linearEquiv (T := T) e.symm)
  · intro hh
    rw [he1, LinearMap.rTensor_comp]
    exact hh.comp (injective_rTensor_linearEquiv (T := T) e)

/-- An injective linear map and the inclusion of its range have the same `T`-purity. -/
theorem injective_rTensor_iff_range {T M N : Type u} [AddCommGroup T] [Module S T]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (f : M →ₗ[S] N)
    (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor T f) ↔
      Function.Injective (LinearMap.rTensor T (Submodule.subtype (LinearMap.range f))) := by
  let e : M ≃ₗ[S] LinearMap.range f :=
    LinearEquiv.ofBijective
      (LinearMap.codRestrict (LinearMap.range f) f (fun x => LinearMap.mem_range.mpr ⟨x, rfl⟩))
      ⟨fun x y hxy => hf (Subtype.ext_iff.mp hxy),
        fun y => by
          obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
          exact ⟨x, Subtype.ext hx⟩⟩
  have hunfold : LinearMap.rTensor T f =
      (LinearMap.rTensor T (Submodule.subtype (LinearMap.range f))).comp
        (LinearMap.rTensor T (e : M →ₗ[S] _)) := by
    have h1 : f = (Submodule.subtype (LinearMap.range f)).comp (e : M →ₗ[S] _) := by
      ext x
      rfl
    conv_lhs => rw [h1]
    rw [LinearMap.rTensor_comp]
  have hbij : Function.Bijective
      (LinearMap.rTensor T (e : M →ₗ[S] LinearMap.range f)) :=
    ⟨injective_rTensor_linearEquiv (T := T) e, surjective_rTensor_linearEquiv (T := T) e⟩
  rw [hunfold]
  exact Function.Injective.of_comp_iff'
    (LinearMap.rTensor T (Submodule.subtype (LinearMap.range f))) hbij

/-! ## The abstract diagram chase -/
/-- **Diagram chase.**  Suppose `b ∘ a = f`, `c ∘ a = 0`, that `ker (b ⊗ id_T)` is the image of
`k ⊗ id_T` (as produced by right exactness of `⊗[S] T`), and that `(c ∘ k) ⊗ id_T` and
`a ⊗ id_T` are injective.  Then `f ⊗ id_T` is injective. -/
theorem injective_rTensor_of_chase {T A Q P F K : Type u}
    [AddCommGroup T] [Module S T] [AddCommGroup A] [Module S A] [AddCommGroup Q] [Module S Q]
    [AddCommGroup P] [Module S P] [AddCommGroup F] [Module S F] [AddCommGroup K] [Module S K]
    (f : A →ₗ[S] Q) (a : A →ₗ[S] P) (k : K →ₗ[S] P) (b : P →ₗ[S] Q) (c : P →ₗ[S] F)
    (hb : b ∘ₗ a = f) (hc : c ∘ₗ a = 0)
    (hker : LinearMap.ker (LinearMap.rTensor T b) = LinearMap.range (LinearMap.rTensor T k))
    (hk : Function.Injective (LinearMap.rTensor T (c ∘ₗ k)))
    (ha : Function.Injective (LinearMap.rTensor T a)) :
    Function.Injective (LinearMap.rTensor T f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h1 : (LinearMap.rTensor T (b ∘ₗ a)) x = 0 := by rw [hb]; exact hx
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply] at h1
  have hmem : LinearMap.rTensor T a x ∈ LinearMap.range (LinearMap.rTensor T k) := by
    rw [← hker]; exact LinearMap.mem_ker.mpr h1
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hmem
  have h2 : (LinearMap.rTensor T (c ∘ₗ a)) x = 0 := by rw [hc]; simp
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply] at h2
  have h3 : LinearMap.rTensor T (c ∘ₗ k) z = 0 := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hz]; exact h2
  have h4 : z = 0 := hk (by rw [h3, map_zero])
  have h6 : (LinearMap.rTensor T a) x = (LinearMap.rTensor T a) 0 := by
    rw [← hz, h4]; simp
  exact ha h6

/-! ## The fibre product of two linear maps with a common codomain -/

section Pullback

variable {B W C : Type u} [AddCommGroup B] [Module S B] [AddCommGroup W] [Module S W]
  [AddCommGroup C] [Module S C]

/-- The fibre product `{(b, w) | φ b = θ w} ⊆ B × W` of `φ` and `θ`. -/
def pullback (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) : Submodule S (B × W) :=
  LinearMap.ker ((φ.comp (LinearMap.fst S B W)) - (θ.comp (LinearMap.snd S B W)))

lemma mem_pullback {φ : B →ₗ[S] C} {θ : W →ₗ[S] C} {x : B × W} :
    x ∈ pullback φ θ ↔ φ x.1 = θ x.2 := by
  simp [pullback, sub_eq_zero]

/-- The first projection of the fibre product. -/
def pullbackFst (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) : pullback φ θ →ₗ[S] B :=
  (LinearMap.fst S B W).comp (pullback φ θ).subtype

/-- The second projection of the fibre product. -/
def pullbackSnd (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) : pullback φ θ →ₗ[S] W :=
  (LinearMap.snd S B W).comp (pullback φ θ).subtype

@[simp] lemma pullbackFst_apply (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) (x : pullback φ θ) :
    pullbackFst φ θ x = (x : B × W).1 := rfl

@[simp] lemma pullbackSnd_apply (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) (x : pullback φ θ) :
    pullbackSnd φ θ x = (x : B × W).2 := rfl

/-- `ker φ` sits in the fibre product as `b ↦ (b, 0)`. -/
def pullbackKerSnd (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) : LinearMap.ker φ →ₗ[S] pullback φ θ :=
  LinearMap.codRestrict (pullback φ θ) ((LinearMap.inl S B W).comp (LinearMap.ker φ).subtype)
    (fun x => by
      rw [LinearMap.comp_apply, mem_pullback]
      simp [LinearMap.mem_ker.mp x.2])

/-- `ker θ` sits in the fibre product as `w ↦ (0, w)`. -/
def pullbackKerFst (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) : LinearMap.ker θ →ₗ[S] pullback φ θ :=
  LinearMap.codRestrict (pullback φ θ) ((LinearMap.inr S B W).comp (LinearMap.ker θ).subtype)
    (fun x => by
      rw [LinearMap.comp_apply, mem_pullback]
      simp [LinearMap.mem_ker.mp x.2])

lemma pullbackSnd_comp_pullbackKerFst (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) :
    (pullbackSnd φ θ).comp (pullbackKerFst φ θ) = (LinearMap.ker θ).subtype := by
  ext x
  rfl

lemma pullbackFst_comp_pullbackKerSnd (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) :
    (pullbackFst φ θ).comp (pullbackKerSnd φ θ) = (LinearMap.ker φ).subtype := by
  ext x
  rfl

lemma pullbackFst_surjective (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) (hθ : Function.Surjective θ) :
    Function.Surjective (pullbackFst φ θ) := by
  intro b
  obtain ⟨w, hw⟩ := hθ (φ b)
  exact ⟨⟨(b, w), by rw [mem_pullback]; simpa using hw.symm⟩, rfl⟩

lemma pullbackSnd_surjective (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) (hφ : Function.Surjective φ) :
    Function.Surjective (pullbackSnd φ θ) := by
  intro w
  obtain ⟨b, hb⟩ := hφ (θ w)
  exact ⟨⟨(b, w), by rw [mem_pullback]; simpa using hb⟩, rfl⟩

lemma ker_pullbackFst (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) :
    LinearMap.ker (pullbackFst φ θ) = LinearMap.range (pullbackKerFst φ θ) := by
  ext x
  constructor
  · intro hx
    have h1 : (x : B × W).1 = 0 := hx
    refine LinearMap.mem_range.mpr ⟨⟨(x : B × W).2, ?_⟩, ?_⟩
    · have h2 := mem_pullback.mp x.2
      rw [LinearMap.mem_ker, ← h2, h1, map_zero]
    · refine Subtype.ext ?_
      exact Prod.ext h1.symm rfl
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (by rfl)

lemma ker_pullbackSnd (φ : B →ₗ[S] C) (θ : W →ₗ[S] C) :
    LinearMap.ker (pullbackSnd φ θ) = LinearMap.range (pullbackKerSnd φ θ) := by
  ext x
  constructor
  · intro hx
    have h1 : (x : B × W).2 = 0 := hx
    refine LinearMap.mem_range.mpr ⟨⟨(x : B × W).1, ?_⟩, ?_⟩
    · have h2 := mem_pullback.mp x.2
      rw [LinearMap.mem_ker, h2, h1, map_zero]
    · refine Subtype.ext ?_
      exact Prod.ext rfl h1.symm
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (by rfl)

end Pullback

/-! ## A surjection with projective codomain has a `T`-pure kernel -/

theorem injective_rTensor_ker_subtype {T M E : Type u} [AddCommGroup T] [Module S T]
    [AddCommGroup M] [Module S M] [AddCommGroup E] [Module S E] [Module.Projective S E]
    (α : M →ₗ[S] E) (hα : Function.Surjective α) :
    Function.Injective (LinearMap.rTensor T (Submodule.subtype (LinearMap.ker α))) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective α (LinearMap.range_eq_top.mpr hα)
  have hgy : ∀ y : E, α (g y) = y := by
    intro y
    have h := LinearMap.congr_fun hg y
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at h
  have hmem : ∀ m : M, ((LinearMap.id - g.comp α : M →ₗ[S] M)) m ∈ LinearMap.ker α := by
    intro m
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hgy (α m), sub_self]
  let r : M →ₗ[S] LinearMap.ker α :=
    LinearMap.codRestrict (LinearMap.ker α) (LinearMap.id - g.comp α : M →ₗ[S] M) hmem
  have hr : r.comp (Submodule.subtype (LinearMap.ker α)) = LinearMap.id := by
    ext x
    show ((LinearMap.id - g.comp α : M →ₗ[S] M)) (x : M) = (x : M)
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2,
      map_zero, sub_zero]
  exact TPure.of_retract (T := T) hr

/-! ## The case of a finite free cokernel -/

/-- Evaluation at `i` is surjective. -/
theorem proj_fin_surjective (I : Ideal S) {n : ℕ} (i : Fin n) :
    Function.Surjective (LinearMap.proj (R := S) (φ := fun _ : Fin n => S ⧸ I) i) :=
  LinearMap.proj_surjective (R := S) (φ := fun _ : Fin n => S ⧸ I) i

/-- If `ψ : Q →ₗ (Fin n → S ⧸ I)` is surjective, then `ker ψ ↪ Q` is `T`-pure.  This is the
finitely generated version of `tpure_of_coker_quot`, obtained by peeling off one coordinate at a
time. -/
theorem injective_rTensor_ker_fin_aux (I : Ideal S) {T : Type u} [AddCommGroup T] [Module S T]
    (h1 : IdxInj I T) :
    ∀ n : ℕ, ∀ (Q : Type u) [AddCommGroup Q] [Module S Q]
      (ψ : Q →ₗ[S] (Fin n → (S ⧸ I))), Function.Surjective ψ →
      Function.Injective (LinearMap.rTensor T (Submodule.subtype (LinearMap.ker ψ))) := by
  intro n
  induction n with
  | zero =>
      intro Q _ _ ψ hψ
      have hsub : Subsingleton (Fin 0 → (S ⧸ I)) := inferInstance
      haveI := hsub
      have h0 : ψ = 0 := Subsingleton.elim _ _
      rw [h0, LinearMap.ker_zero]
      exact injective_rTensor_subtype_top (T := T)
  | succ n ih =>
      intro Q _ _ ψ hψ
      let proj0 : (Fin (n + 1) → (S ⧸ I)) →ₗ[S] (S ⧸ I) :=
        LinearMap.proj (R := S) (φ := fun _ : Fin (n + 1) => S ⧸ I) 0
      have hproj0 : Function.Surjective proj0 := proj_fin_surjective I 0
      have hprojsurj : Function.Surjective (proj0.comp ψ) := hproj0.comp hψ
      have hX : Function.Injective
          (LinearMap.rTensor T
            (Submodule.subtype (LinearMap.ker (proj0.comp ψ)))) :=
        tpure_of_coker_quot I _ _ rfl hprojsurj T h1
      let ψ' : LinearMap.ker (proj0.comp ψ) →ₗ[S] (Fin n → (S ⧸ I)) :=
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (R := S) (φ := fun _ : Fin (n + 1) => S ⧸ I) i.succ).comp
            (ψ.comp (Submodule.subtype _)))
      have hψ' : Function.Surjective ψ' := by
        intro g
        obtain ⟨y, hy⟩ := hψ (Fin.cons 0 g)
        refine ⟨⟨y, ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.proj_apply, hy, Fin.cons_zero]
        · ext i
          show (ψ y) i.succ = g i
          rw [hy, Fin.cons_succ]
      have hker' : LinearMap.ker ψ' =
          (LinearMap.ker ψ).comap (Submodule.subtype (LinearMap.ker (proj0.comp ψ))) := by
        ext x
        constructor
        · intro hx
          show ψ (x : Q) = 0
          have hx' : ψ' x = 0 := LinearMap.mem_ker.mp hx
          have htail : ∀ i : Fin n, ψ (x : Q) i.succ = 0 := by
            intro i
            have h1 : ψ' x i = 0 := by rw [hx']; rfl
            simpa only [ψ', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
              Submodule.subtype_apply, Pi.zero_apply] using h1
          have h0 : ψ (x : Q) 0 = 0 := x.2
          funext i
          exact Fin.cases h0 (fun j => htail j) i
        · intro hx
          show ψ' x = 0
          have hz : ψ (x : Q) = 0 := LinearMap.mem_ker.mp hx
          ext i
          have h1 : ψ (x : Q) i.succ = 0 := by rw [hz]; rfl
          simpa only [ψ', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
            Submodule.subtype_apply, Pi.zero_apply] using h1
      have ih' := ih _ ψ' hψ'
      rw [hker'] at ih'
      have hle : LinearMap.ker ψ ≤ LinearMap.ker (proj0.comp ψ) :=
        LinearMap.ker_le_ker_comp ψ proj0
      have hstep : Function.Injective
          (LinearMap.rTensor T (Submodule.inclusion hle)) :=
        (rTensor_inclusion_iff_rTensor_comap (T := T) hle).mpr ih'
      rw [← Submodule.subtype_comp_inclusion (LinearMap.ker ψ) (LinearMap.ker (proj0.comp ψ))
        hle, LinearMap.rTensor_comp]
      exact hX.comp hstep

/-- If `ψ : Q →ₗ (Fin n → S ⧸ I)` is surjective, then `ker ψ ↪ Q` is `T`-pure. -/
theorem injective_rTensor_ker_fin (I : Ideal S) (n : ℕ) {T : Type u} [AddCommGroup T] [Module S T]
    (h1 : IdxInj I T) {Q : Type u} [AddCommGroup Q] [Module S Q]
    (ψ : Q →ₗ[S] (Fin n → (S ⧸ I))) (hψ : Function.Surjective ψ) :
    Function.Injective (LinearMap.rTensor T (Submodule.subtype (LinearMap.ker ψ))) :=
  injective_rTensor_ker_fin_aux I h1 n Q ψ hψ

/-! ## The case of a finitely generated cokernel -/

/-- The module `Fin n → S ⧸ I` is killed by `I`. -/
theorem smul_top_fin_quot_eq_bot (I : Ideal S) (n : ℕ) :
    I • (⊤ : Submodule S (Fin n → (S ⧸ I))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hle : I • (⊤ : Submodule S (Fin n → (S ⧸ I))) ≤ ⊥ := by
    rw [Submodule.smul_le]
    intro i hi g _
    show i • g = 0
    funext j
    show i • (g j) = 0
    rw [Algebra.smul_def,
      show (algebraMap S (S ⧸ I)) i = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_mul]
  simpa using hle hf

/-- **Finitely generated cokernel.**  If `A ≤ Q` and `Q ⧸ A` is a quotient of the free
`S ⧸ I`-module `Fin n → S ⧸ I`, then `A ↪ Q` is `T`-pure.

The proof uses the fibre product `P := Q ×_{Q ⧸ A} (Fin n → S ⧸ I)` of `A.mkQ` and `π`.  Then
`P ⧸ A ≅ Fin n → S ⧸ I` (so `A ↪ P` is `T`-pure by the previous lemma) while
`P ⧸ (ker π) ≅ Q` and `ker π ↪ Fin n → S ⧸ I` is `T`-pure by `tpure_of_flat_quot_top`; the
diagram chase `injective_rTensor_of_chase` finishes. -/
theorem injective_rTensor_subtype_of_fin_quotient (I : Ideal S) {T : Type u} [AddCommGroup T]
    [Module S T] (h1 : IdxInj I T) (h2 : Module.Flat (S ⧸ I) (T ⧸ (I • ⊤ : Submodule S T)))
    {Q : Type u} [AddCommGroup Q] [Module S Q] (A : Submodule S Q) {n : ℕ}
    (π : (Fin n → (S ⧸ I)) →ₗ[S] (Q ⧸ A)) (hπ : Function.Surjective π) :
    Function.Injective (LinearMap.rTensor T (Submodule.subtype A)) := by
  let φ : Q →ₗ[S] (Q ⧸ A) := A.mkQ
  let P : Submodule S (Q × (Fin n → (S ⧸ I))) := pullback φ π
  let b : P →ₗ[S] Q := pullbackFst φ π
  let c : P →ₗ[S] (Fin n → (S ⧸ I)) := pullbackSnd φ π
  let a : LinearMap.ker φ →ₗ[S] P := pullbackKerSnd φ π
  let k : LinearMap.ker π →ₗ[S] P := pullbackKerFst φ π
  have hφsurj : Function.Surjective φ := Submodule.mkQ_surjective A
  have hb : Function.Surjective b := pullbackFst_surjective φ π hπ
  have hc : Function.Surjective c := pullbackSnd_surjective φ π hφsurj
  have hex : Function.Exact k b := LinearMap.exact_iff.mpr (ker_pullbackFst φ π)
  have hker : LinearMap.ker (LinearMap.rTensor T b) = LinearMap.range (LinearMap.rTensor T k) :=
    LinearMap.exact_iff.mp (rTensor_exact T hex hb)
  have hk : Function.Injective (LinearMap.rTensor T (c.comp k)) := by
    rw [show c.comp k = (LinearMap.ker π).subtype from pullbackSnd_comp_pullbackKerFst φ π]
    exact tpure_of_flat_quot_top I (smul_top_fin_quot_eq_bot I n) (LinearMap.ker π) T h2
  have hsnd : Function.Injective (LinearMap.rTensor T (Submodule.subtype (LinearMap.ker c))) :=
    injective_rTensor_ker_fin I n h1 c hc
  -- `ker φ` is, via `a`, canonically `ker c`.
  have hmem : ∀ x : LinearMap.ker φ, a x ∈ LinearMap.ker c := by
    intro x
    rw [LinearMap.mem_ker]
    rfl
  have hmem' : ∀ y : LinearMap.ker c,
      (((y : P)) : Q × (Fin n → (S ⧸ I))).1 ∈ LinearMap.ker φ := by
    intro y
    rw [LinearMap.mem_ker]
    have h2' := mem_pullback.mp (y : P).2
    have hy2 : (((y : P)) : Q × (Fin n → (S ⧸ I))).2 = 0 := y.2
    show φ ((((y : P)) : Q × (Fin n → (S ⧸ I))).1) = 0
    rw [h2', hy2, map_zero]
  let a' : LinearMap.ker φ →ₗ[S] LinearMap.ker c := LinearMap.codRestrict _ a hmem
  have ha'inj : Function.Injective a' := by
    intro x y hxy
    have h1 : a x = a y := congrArg Subtype.val hxy
    refine Subtype.ext ?_
    have h2' := congrArg (fun z : P => (z : Q × (Fin n → (S ⧸ I))).1) h1
    simpa [a, pullbackKerSnd] using h2'
  have ha'surj : Function.Surjective a' := by
    intro y
    have hy : (y : P) ∈ LinearMap.range a := by
      rw [show LinearMap.range a = LinearMap.ker c from (ker_pullbackSnd φ π).symm]
      exact y.2
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  let e : LinearMap.ker φ ≃ₗ[S] LinearMap.ker c := LinearEquiv.ofBijective a' ⟨ha'inj, ha'surj⟩
  have hfac : (Submodule.subtype (LinearMap.ker c)).comp (e : LinearMap.ker φ →ₗ[S] _) = a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  have ha : Function.Injective (LinearMap.rTensor T a) := by
    refine (injective_rTensor_iff_range (T := T) a ?_).mpr ?_
    · intro x y hxy
      refine Subtype.ext ?_
      have h1 : ((a x : P) : Q × (Fin n → (S ⧸ I))).1 =
          ((a y : P) : Q × (Fin n → (S ⧸ I))).1 :=
        congrArg (fun z : P => (z : Q × (Fin n → (S ⧸ I))).1) hxy
      simpa [a, pullbackKerSnd] using h1
    · rw [show LinearMap.range a = LinearMap.ker c from (ker_pullbackSnd φ π).symm]
      exact hsnd
  have hb' : b.comp a = (LinearMap.ker φ).subtype :=
    pullbackFst_comp_pullbackKerSnd φ π
  have hc' : c.comp a = 0 := by
    ext x
    rfl
  have hchase : Function.Injective (LinearMap.rTensor T ((LinearMap.ker φ).subtype)) :=
    injective_rTensor_of_chase (Submodule.subtype (LinearMap.ker φ)) a k b c hb' hc' hker hk ha
  rwa [show LinearMap.ker φ = A from Submodule.ker_mkQ A] at hchase

/-- **Step A of Stacks 10.99.8 (tag 051C)**: if the submodule `A ≤ Q` contains `I • ⊤` (equivalently `Q ⧸ A` is killed by `I`), and if `h1 : I ⊗[S] T → T` is injective and `T ⧸ I • ⊤` is flat over `S ⧸ I` (`h2`), then `A ↪ Q` stays injective after `⊗[S] T`; equivalently `Tor₁ˢ(N, T) = 0` for every `S ⧸ I`-module `N`.  (Nilpotence of `I` is NOT needed here.) -/
theorem tpure_of_smul_top_le {S : Type _} [CommRing S] (I : Ideal S) (T : Type _)
    [AddCommGroup T] [Module S T] (h1 : Work.DSFFP.IdxInj I T)
    (h2 : Module.Flat (S ⧸ I) (T ⧸ (I • ⊤ : Submodule S T)))
    {Q : Type _} [AddCommGroup Q] [Module S Q] (A : Submodule S Q)
    (hA : I • (⊤ : Submodule S Q) ≤ A) : Work.DSFFP.TPure T A.subtype := by
  classical
  rw [TPure]
  let φ : Q →ₗ[S] (Q ⧸ A) := A.mkQ
  have hφsurj : Function.Surjective φ := Submodule.mkQ_surjective A
  have hkill : ∀ x : Q, ∀ r ∈ I, r • x ∈ A := fun x r hr => (Submodule.smul_le.mp hA) r hr x trivial
  have hIC : Module.IsTorsionBySet S (Q ⧸ A) (I : Set S) :=
    (Module.isTorsionBySet_quotient_iff A (I : Set S)).mpr fun x r hr => hkill x r hr
  letI : Module (S ⧸ I) (Q ⧸ A) := Module.IsTorsionBySet.module hIC
  -- The directed family of preimages of the finitely generated submodules of `Q ⧸ A`
  have hle : ∀ s : Finset (Q ⧸ A), A ≤ (Submodule.span S ((s : Set (Q ⧸ A)))).comap φ := by
    intro s a ha
    rw [Submodule.mem_comap]
    have h0 : φ a = 0 := by
      have : Submodule.Quotient.mk (p := A) a = 0 := (Submodule.Quotient.mk_eq_zero A).mpr ha
      simpa [φ, Submodule.mkQ_apply] using this
    rw [h0]
    exact Submodule.zero_mem _
  have hmono : Monotone fun s : Finset (Q ⧸ A) => (Submodule.span S ((s : Set (Q ⧸ A)))).comap φ :=
    fun s t hst => Submodule.comap_mono (Submodule.span_mono hst)
  have hsup : (⨆ s : Finset (Q ⧸ A), (Submodule.span S ((s : Set (Q ⧸ A)))).comap φ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine Submodule.mem_iSup_of_mem ({φ x} : Finset (Q ⧸ A)) ?_
    rw [Submodule.mem_comap]
    exact Submodule.subset_span (by simp)
  -- Each finite piece has a finitely generated cokernel, so the f.g. case applies
  have key : ∀ s : Finset (Q ⧸ A), Function.Injective
      (LinearMap.rTensor T (Submodule.inclusion (hle s))) := by
    intro s
    let Qs : Submodule S Q := (Submodule.span S ((s : Set (Q ⧸ A)))).comap φ
    have hAs : A ≤ Qs := hle s
    let As : Submodule S ↥Qs := A.comap (Submodule.subtype Qs)
    -- lifts of the elements of `s`
    have hex : ∀ c : (s : Set (Q ⧸ A)), ∃ q : Q, φ q = (c : Q ⧸ A) :=
      fun c => hφsurj (c : Q ⧸ A)
    choose lift hlift using hex
    have hmem_lift : ∀ c : (s : Set (Q ⧸ A)), lift c ∈ Qs := by
      intro c
      rw [Submodule.mem_comap, hlift c]
      exact Submodule.subset_span c.2
    -- the `Fin s.card → S ⧸ I`-module structure
    have hIQ : I • (⊤ : Submodule S ↥Qs) ≤ As := by
      rw [Submodule.smul_le]
      intro r hr y _
      rw [Submodule.mem_comap]
      exact hkill (y : Q) r hr
    have hts : Module.IsTorsionBySet S (↥Qs ⧸ As) (I : Set S) :=
      (Module.isTorsionBySet_quotient_iff As (I : Set S)).mpr fun x r hr =>
        (Submodule.smul_le.mp hIQ) r hr x trivial
    letI : Module (S ⧸ I) (↥Qs ⧸ As) := Module.IsTorsionBySet.module hts
    let e : (s : Set (Q ⧸ A)) ≃ Fin s.card := Finset.equivFin s
    let πs : (Fin s.card → (S ⧸ I)) →ₗ[S] (↥Qs ⧸ As) :=
      ∑ c : (s : Set (Q ⧸ A)),
        ((LinearMap.proj (R := S) (φ := fun _ : Fin s.card => S ⧸ I) (e c)).smulRight
          (As.mkQ ⟨lift c, hmem_lift c⟩))
    have hπs : Function.Surjective πs := by
      intro y
      obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective As y
      have hq : φ (q : Q) ∈ Submodule.span S ((s : Set (Q ⧸ A))) :=
        Submodule.mem_comap.mp q.2
      obtain ⟨f, hfsupp, hfsum⟩ := (Submodule.mem_span_finset).mp hq
      refine ⟨fun i => Ideal.Quotient.mk I
        (f ((e.symm i : (s : Set (Q ⧸ A))) : Q ⧸ A)), ?_⟩
      have h1 : πs (fun i => Ideal.Quotient.mk I
            (f ((e.symm i : (s : Set (Q ⧸ A))) : Q ⧸ A))) =
          ∑ c : (s : Set (Q ⧸ A)),
            Ideal.Quotient.mk I (f (c : Q ⧸ A)) • (As.mkQ ⟨lift c, hmem_lift c⟩) := by
        show (∑ c : (s : Set (Q ⧸ A)),
            ((LinearMap.proj (R := S) (φ := fun _ : Fin s.card => S ⧸ I) (e c)).smulRight
              (As.mkQ ⟨lift c, hmem_lift c⟩)))
            (fun i => Ideal.Quotient.mk I
              (f ((e.symm i : (s : Set (Q ⧸ A))) : Q ⧸ A))) = _
        rw [LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [LinearMap.smulRight_apply, LinearMap.proj_apply]
        congr 1
        rw [show e.symm (e c) = c from e.symm_apply_apply c]
      rw [h1]
      -- the same element expressed via `q`
      have hsum_mem : (∑ c : (s : Set (Q ⧸ A)), f (c : Q ⧸ A) • lift c) ∈ Qs :=
        Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hmem_lift c)
      have hsum_eq : (∑ c : (s : Set (Q ⧸ A)), f (c : Q ⧸ A) • (c : Q ⧸ A)) = φ (q : Q) := by
        rw [← hfsum]
        exact Finset.sum_coe_sort s fun a => f a • a
      have hdiff : (q - ⟨_, hsum_mem⟩ : ↥Qs) ∈ As := by
        rw [Submodule.mem_comap]
        have hmem : (Submodule.subtype Qs (q - ⟨_, hsum_mem⟩) : Q) ∈ LinearMap.ker φ := by
          rw [LinearMap.mem_ker]
          show φ ((q : Q) - ∑ c : (s : Set (Q ⧸ A)), f (c : Q ⧸ A) • lift c) = 0
          rw [map_sub, sub_eq_zero, map_sum, ← hsum_eq]
          exact Finset.sum_congr rfl fun c _ => by rw [map_smul, hlift c]
        rwa [Submodule.ker_mkQ A] at hmem
      rw [show As.mkQ q = As.mkQ ⟨_, hsum_mem⟩ from (Submodule.Quotient.eq As).mpr hdiff]
      rw [show (⟨_, hsum_mem⟩ : ↥Qs) = ∑ c : (s : Set (Q ⧸ A)),
            (⟨f (c : Q ⧸ A) • lift c, Submodule.smul_mem _ _ (hmem_lift c)⟩ : ↥Qs)
          from Subtype.ext (by simp)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      show (Ideal.Quotient.mk I (f (c : Q ⧸ A))) • (As.mkQ ⟨lift c, hmem_lift c⟩) =
        As.mkQ (f (c : Q ⧸ A) • (⟨lift c, hmem_lift c⟩ : ↥Qs))
      rw [map_smul]
      exact Module.IsTorsionBySet.mk_smul hts (f (c : Q ⧸ A))
        (As.mkQ ⟨lift c, hmem_lift c⟩)
    have hfg := injective_rTensor_subtype_of_fin_quotient I h1 h2 As πs hπs
    exact (rTensor_inclusion_iff_rTensor_comap (T := T) (hle s)).mpr hfg
  exact tpure_of_iSup A _ hmono hle hsup T key

end Work.DSFFP
