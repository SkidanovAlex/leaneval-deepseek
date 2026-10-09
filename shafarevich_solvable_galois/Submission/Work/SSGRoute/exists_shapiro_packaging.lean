import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.shapiro_induce_two_cocycle

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped TensorProduct

variable {p : ℕ} {G : Type*} [Group G]

/-- A `G`-equivariant `𝔽_p`-linear map between two `𝔽_p[G]`-modules carries `2`-cocycles to
`2`-cocycles. -/
theorem mem_Z2_comp_of_equivariant
    {A B : Type*} [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
    (ψ : A →ₗ[ZMod p] B) (hψ : ∀ (g : G) (a : A), ψ (g • a) = g • ψ a)
    (c : G × G → A) (hc : c ∈ Work.GroupCohomology.Z2 G A) :
    (fun q => ψ (c q)) ∈ Work.GroupCohomology.Z2 G B := by
  rw [Work.GroupCohomology.mem_Z2_iff] at hc ⊢
  intro g h k
  have h1 : c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k) := hc g h k
  calc ψ (c (g * h, k)) + ψ (c (g, h))
      = ψ (c (g * h, k) + c (g, h)) := by rw [map_add]
    _ = ψ (g • c (h, k) + c (g, h * k)) := by rw [h1]
    _ = g • ψ (c (h, k)) + ψ (c (g, h * k)) := by rw [map_add, hψ]

/-- `LinearMap.lTensor` of a `G`-equivariant linear map is `G`-equivariant for the diagonal
`G`-actions on tensor products. -/
theorem lTensor_equivariant
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    {N N' : Type*} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [AddCommGroup N'] [Module (ZMod p) N']
    [DistribMulAction G N'] [SMulCommClass G (ZMod p) N']
    (f : N →ₗ[ZMod p] N') (hf : ∀ (g : G) (n : N), f (g • n) = g • f n) (g : G)
    (x : M ⊗[ZMod p] N) :
    (LinearMap.lTensor M f) (g • x) = g • (LinearMap.lTensor M f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [Work.Shrinking.diagTensor_smul_tmul, LinearMap.lTensor_tmul, hf,
        LinearMap.lTensor_tmul, Work.Shrinking.diagTensor_smul_tmul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The coordinate insertion `LinearMap.single` is `G`-equivariant for the pointwise action. -/
theorem single_equivariant {ι : Type*} [DecidableEq ι] {φ : ι → Type*}
    [∀ i, AddCommGroup (φ i)] [∀ i, Module (ZMod p) (φ i)] [∀ i, DistribMulAction G (φ i)]
    (a : ι) (g : G) (v : φ a) :
    (LinearMap.single (ZMod p) φ a) (g • v) = g • (LinearMap.single (ZMod p) φ a) v := by
  rw [LinearMap.single_apply, LinearMap.single_apply, Pi.single_smul]

/-- The coordinate projection is a left inverse of the coordinate insertion inside a tensor
product. -/
theorem lTensor_proj_single_apply {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    {ι : Type*} [DecidableEq ι] {φ : ι → Type*}
    [∀ i, AddCommGroup (φ i)] [∀ i, Module (ZMod p) (φ i)] (a : ι)
    (x : M ⊗[ZMod p] φ a) :
    (LinearMap.lTensor M (LinearMap.proj a))
      ((LinearMap.lTensor M (LinearMap.single (ZMod p) φ a)) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m t =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.single_apply,
        LinearMap.proj_apply, Pi.single_eq_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Shapiro packaging for a `Fin n`-indexed family.** For a finite family of subgroups
`H i ≤ G` and `2`-cocycles `κ i` on `H i` with values in an `𝔽_p[G]`-module `M`, there is a
finitely generated `𝔽_p[G]`-module `T` (the `Fin n`-indexed product of the individual Shapiro
modules, hence a small type) together with `H i`-equivariant maps `ev i : M ⊗ T → M` and
`2`-cocycles `C i` on `G` with values in `M ⊗ T` whose values on `H i × H i` reproduce `κ i`. -/
private theorem shapiro_packaging_fin (p : ℕ) (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (H : Fin n → Subgroup G) (κ : ∀ a : Fin n, ↥(H a) × ↥(H a) → M)
    (hκ : ∀ a : Fin n, κ a ∈ Work.GroupCohomology.Z2 (↥(H a)) M) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T) (_ : DistribMulAction G T)
      (_ : SMulCommClass G (ZMod p) T) (_ : Module.Finite (ZMod p) T)
      (ev : ∀ a : Fin n, M ⊗[ZMod p] T →ₗ[ZMod p] M)
      (_ : ∀ (a : Fin n) (h : ↥(H a)) (t : M ⊗[ZMod p] T),
        ev a ((h : G) • t) = (h : G) • ev a t)
      (C : ∀ a : Fin n, G × G → M ⊗[ZMod p] T),
      (∀ a : Fin n, C a ∈ Work.GroupCohomology.Z2 G (M ⊗[ZMod p] T)) ∧
      (∀ (a : Fin n) (h h' : ↥(H a)), ev a (C a ((h : G), (h' : G))) = κ a (h, h')) := by
  classical
  have hfam : ∀ a : Fin n, ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T)
      (_ : DistribMulAction G T) (_ : SMulCommClass G (ZMod p) T) (_ : Module.Finite (ZMod p) T)
      (ev : M ⊗[ZMod p] T →ₗ[ZMod p] M)
      (_ : ∀ (h : ↥(H a)) (x : M ⊗[ZMod p] T), ev ((h : G) • x) = (h : G) • ev x)
      (C : G × G → M ⊗[ZMod p] T),
      C ∈ Work.GroupCohomology.Z2 G (M ⊗[ZMod p] T) ∧
        ∀ h h' : ↥(H a), ev (C ((h : G), (h' : G))) = κ a (h, h') :=
    fun a => shapiro_induce_two_cocycle p G (H a) M (κ a) (hκ a)
  choose T hAdd hMod hAct hComm hFin ev hev Cc hCc hCcv using hfam
  letI : ∀ a, AddCommGroup (T a) := hAdd
  letI : ∀ a, Module (ZMod p) (T a) := hMod
  letI : ∀ a, DistribMulAction G (T a) := hAct
  letI : ∀ a, SMulCommClass G (ZMod p) (T a) := hComm
  letI : ∀ a, Module.Finite (ZMod p) (T a) := hFin
  refine ⟨(∀ a : Fin n, T a), inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.pi, ?ev, ?hev, ?C, ?hC, ?hCval⟩
  case ev =>
    exact fun a => (ev a).comp (LinearMap.lTensor M (LinearMap.proj a))
  case hev =>
    intro a h x
    show (ev a) ((LinearMap.lTensor M (LinearMap.proj a)) ((h : G) • x))
      = (h : G) • (ev a) ((LinearMap.lTensor M (LinearMap.proj a)) x)
    rw [lTensor_equivariant (M := M) (f := LinearMap.proj (φ := T) a) (fun g y => rfl)
      (h : G) x]
    exact hev a h _
  case C =>
    exact fun a q => LinearMap.lTensor M (LinearMap.single (ZMod p) T a) (Cc a q)
  case hC =>
    intro a
    exact mem_Z2_comp_of_equivariant (A := M ⊗[ZMod p] T a) (B := M ⊗[ZMod p] (∀ i, T i))
      (LinearMap.lTensor M (LinearMap.single (ZMod p) T a))
      (fun g x => lTensor_equivariant (M := M) (f := LinearMap.single (ZMod p) T a)
        (fun g' v => single_equivariant a g' v) g x) (Cc a) (hCc a)
  case hCval =>
    intro a h h'
    show (ev a) ((LinearMap.lTensor M (LinearMap.proj a))
      ((LinearMap.lTensor M (LinearMap.single (ZMod p) T a))
        (Cc a ((h : G), (h' : G))))) = κ a (h, h')
    rw [lTensor_proj_single_apply (M := M) a]
    exact hCcv a h h'

/-- Transport of a value of the cocycle family along an equality of indices: the membership
proofs of the subtype elements are irrelevant. -/
private lemma kappa_apply_cast {ι : Type*} {G : Type*} [Group G] {M : Type*}
    (H : ι → Subgroup G) (κ : ∀ a : ι, ↥(H a) × ↥(H a) → M)
    {a a' : ι} (h : a' = a) (x y : ↥(H a))
    (px : (x : G) ∈ H a') (py : (y : G) ∈ H a') :
    κ a' (⟨(x : G), px⟩, ⟨(y : G), py⟩) = κ a (x, y) := by
  subst h
  rfl

/-- **Packaging ("Shapiro" packaging) of a finite family of `2`-cocycles on subgroups.**

Given a finite family of subgroups `H a ≤ G` and `2`-cocycles `κ a` on `H a` with values in the
`𝔽_p[G]`-module `E p G m i j`, there is a *single* finite `𝔽_p[G]`-module `T`, `H a`-equivariant
`𝔽_p`-linear maps `ev a : E ⊗ T → E` and `2`-cocycles `C a` on `G` with values in `E ⊗ T` such
that `ev a (C a (h, h')) = κ a (h, h')` for all `h h' ∈ H a`. -/
theorem exists_shapiro_packaging (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (i j m : ℕ) (ι : Type*) [Fintype ι] (H : ι → Subgroup G)
    (κ : ∀ a : ι, ↥(H a) × ↥(H a) → Work.CohomologicalShrinking.E p G m i j)
    (hκ : ∀ a : ι,
      (letI : DistribMulAction ↥(H a) (Work.CohomologicalShrinking.E p G m i j) :=
        DistribMulAction.compHom _ (Subgroup.subtype _)
       κ a ∈ Work.GroupCohomology.Z2 _ (Work.CohomologicalShrinking.E p G m i j))) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T) (_ : DistribMulAction G T)
      (_ : SMulCommClass G (ZMod p) T) (_ : Module.Finite (ZMod p) T)
      (ev : ∀ a : ι, TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T →ₗ[ZMod p]
        Work.CohomologicalShrinking.E p G m i j)
      (_ : ∀ (a : ι) (h : ↥(H a))
        (t : TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T),
        ev a ((h : G) • t) = (h : G) • ev a t)
      (C : ∀ a : ι, G × G → TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T),
      (∀ a : ι, C a ∈ Work.GroupCohomology.Z2 G
          (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T)) ∧
      (∀ (a : ι) (h h' : ↥(H a)),
        ev a (C a ((h : G), (h' : G))) = κ a (h, h')) := by
  classical
  obtain ⟨T, hAdd, hMod, hAct, hComm, hFin, evf, hevf, Cf, hCf, hCvf⟩ :=
    shapiro_packaging_fin p G (Fintype.card ι) (Work.CohomologicalShrinking.E p G m i j)
      (fun i : Fin (Fintype.card ι) => H ((Fintype.equivFin ι).symm i))
      (fun i : Fin (Fintype.card ι) => κ ((Fintype.equivFin ι).symm i))
      (fun i => hκ ((Fintype.equivFin ι).symm i))
  letI : AddCommGroup T := hAdd
  letI : Module (ZMod p) T := hMod
  letI : DistribMulAction G T := hAct
  letI : SMulCommClass G (ZMod p) T := hComm
  letI : Module.Finite (ZMod p) T := hFin
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (fun a => evf ((Fintype.equivFin ι) a)), ?_, (fun a => Cf ((Fintype.equivFin ι) a)), ?_, ?_⟩
  · intro a h x
    refine hevf ((Fintype.equivFin ι) a) ⟨(h : G), ?_⟩ x
    exact (congrArg H (Equiv.symm_apply_apply (Fintype.equivFin ι) a)).symm ▸ h.property
  · intro a
    exact hCf ((Fintype.equivFin ι) a)
  · intro a h h'
    have hH : H ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) a)) = H a :=
      congrArg H (Equiv.symm_apply_apply (Fintype.equivFin ι) a)
    refine (hCvf ((Fintype.equivFin ι) a)
      ⟨(h : G), hH.symm ▸ h.property⟩ ⟨(h' : G), hH.symm ▸ h'.property⟩).trans ?_
    exact kappa_apply_cast H κ (Equiv.symm_apply_apply (Fintype.equivFin ι) a) h h'
      (hH.symm ▸ h.property) (hH.symm ▸ h'.property)

end Work.SSGRoute
