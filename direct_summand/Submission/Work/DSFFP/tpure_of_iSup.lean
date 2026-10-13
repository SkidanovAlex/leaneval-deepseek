import Mathlib
import Submission.Work.DSFFP.Defs

open TensorProduct
open scoped TensorProduct

-- `haveI` is used to register the `DirectedSystem` instance of the increasing family of
-- submodules; the style linter suggests `have` there, which would break instance resolution.
set_option linter.style.haveILetI false

namespace Work.DSFFP

universe u v

/-!
### Tensor product, filtered unions, and `T`-purity

We prove `Work.DSFFP.tpure_of_iSup`: if `A ⊆ B i ⊆ Q` with `(B i)` an increasing (`Monotone`)
family of submodules whose union is `Q`, and if the inclusion `A ↪ B i` is `T`-pure for every `i`
(i.e. `A ⊗[S] T → B i ⊗[S] T` is injective), then `A ↪ Q` is `T`-pure as well.

The mathematical content is that `⊗[S] T` commutes with the filtered colimit
`Q = ⋃ i, B i = lim i, B i`; the crucial step is that the canonical map

`limᵢ (B i ⊗[S] T) → Q ⊗[S] T`, `[b ⊗ t] ↦ b ⊗ t`

is injective.  It is an isomorphism: `limᵢ (B i ⊗[S] T) ≃ (limᵢ B i) ⊗[S] T` is Mathlib's
`TensorProduct.directLimitLeft` and `limᵢ B i ≃ Q` (the "union" cocone, injective because each
inclusion `B i ⊆ Q` is injective, surjective because `⨆ i, B i = ⊤`), so it is the tensor product
of two `≃ₗ`.  The proof of the main theorem then proceeds by an element chase: an element
`z ∈ A ⊗[S] T` killed by `A ⊗[S] T → Q ⊗[S] T` is killed already "at a finite stage": its class in
`limᵢ (B i ⊗[S] T)` is `0`, hence by `Module.DirectLimit.of.zero_exact` its image in some
`B j ⊗[S] T` is `0`, and `T`-purity of `A ↪ B j` finishes.
-/

/-- The directed system given by an increasing (`Monotone`) family of submodules `B` of `Q`,
with the inclusion maps `B i →ₗ[S] B j` for `i ≤ j`. -/
noncomputable def iSupColimSystem {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] (B : ι → Submodule S Q) (hBmono : Monotone B) :
    ∀ i j, i ≤ j → B i →ₗ[S] B j :=
  fun _ _ h => Submodule.inclusion (hBmono h)

lemma iSupColimSystem_directedSystem {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] (B : ι → Submodule S Q) (hBmono : Monotone B) :
    DirectedSystem (fun i => B i) (fun i j h => ⇑(iSupColimSystem B hBmono i j h)) :=
  ⟨fun i x => by simp [iSupColimSystem, Submodule.inclusion_apply],
   fun i j k hij hjk x => by simp [iSupColimSystem, Submodule.inclusion_apply]⟩

/-- The canonical map from the direct limit of an increasing family of submodules
(`⋃ i, B i`, computed as `limᵢ B i`) to the ambient module `Q`. -/
noncomputable def iSupColimLift {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] (B : ι → Submodule S Q)
    (hBmono : Monotone B) :
    Module.DirectLimit (fun i => B i) (iSupColimSystem B hBmono) →ₗ[S] Q :=
  Module.DirectLimit.lift S ι (fun i => B i) (iSupColimSystem B hBmono)
    (fun i => Submodule.subtype (B i))
    (fun i j hij x => by simp [iSupColimSystem, Submodule.inclusion_apply])

@[simp]
lemma iSupColimLift_of {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q] [Module S Q]
    {ι : Type v} [Preorder ι] [DecidableEq ι] (B : ι → Submodule S Q) (hBmono : Monotone B)
    (i : ι) (x : B i) :
    iSupColimLift B hBmono
      (Module.DirectLimit.of S ι (fun i => B i) (iSupColimSystem B hBmono) i x) = x :=
  Module.DirectLimit.lift_of (R := S) (ι := ι) (G := fun i => B i)
    (f := iSupColimSystem B hBmono) (g := fun i => Submodule.subtype (B i))
    (Hg := fun i j hij x => by simp [iSupColimSystem, Submodule.inclusion_apply]) x

lemma iSupColimLift_injective {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) :
    Function.Injective (iSupColimLift B hBmono) :=
  Module.DirectLimit.lift_injective (R := S) (ι := ι) (G := fun i => B i)
    (f := iSupColimSystem B hBmono) (P := Q) (g := fun i => Submodule.subtype (B i))
    (Hg := fun i j hij x => by simp [iSupColimSystem, Submodule.inclusion_apply])
    (fun i => Submodule.subtype_injective (B i))

lemma iSupColimLift_surjective {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hB : (⨆ i, B i) = ⊤) :
    Function.Surjective (iSupColimLift B hBmono) := by
  intro q
  have hdir : Directed (· ≤ ·) B := hBmono.directed_le
  have hq : q ∈ ⨆ i, B i := by rw [hB]; trivial
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed B hdir).mp hq
  exact ⟨Module.DirectLimit.of S ι (fun i => B i) (iSupColimSystem B hBmono) i ⟨q, hi⟩,
    by simp⟩

/-- If `⋃ i, B i = ⊤`, then the direct limit of the increasing family `B` is `Q` itself. -/
noncomputable def iSupColimEquiv {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hB : (⨆ i, B i) = ⊤) :
    Module.DirectLimit (fun i => B i) (iSupColimSystem B hBmono) ≃ₗ[S] Q :=
  LinearEquiv.ofBijective (iSupColimLift B hBmono)
    ⟨iSupColimLift_injective B hBmono, iSupColimLift_surjective B hBmono hB⟩

@[simp]
lemma iSupColimEquiv_of {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q] [Module S Q]
    {ι : Type v} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hB : (⨆ i, B i) = ⊤) (i : ι) (x : B i) :
    iSupColimEquiv B hBmono hB
      (Module.DirectLimit.of S ι (fun i => B i) (iSupColimSystem B hBmono) i x) = x :=
  iSupColimLift_of B hBmono i x

/-- Tensoring the isomorphism `limᵢ B i ≃ Q` with `T` identifies `Q ⊗[S] T` with the direct
limit of the `B i ⊗[S] T`.  This is the precise sense in which `⊗[S] T` commutes with the
filtered union `Q = ⋃ i, B i`. -/
noncomputable def iSupColimTensorEquiv {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hB : (⨆ i, B i) = ⊤) (T : Type u)
    [AddCommGroup T] [Module S T] :
    Module.DirectLimit (fun i => B i ⊗[S] T)
      (fun i j h => (iSupColimSystem B hBmono i j h).rTensor T) ≃ₗ[S] Q ⊗[S] T :=
  (TensorProduct.directLimitLeft (iSupColimSystem B hBmono) T).symm ≪≫ₗ
    (iSupColimEquiv B hBmono hB).rTensor T

@[simp]
lemma iSupColimTensorEquiv_of {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {ι : Type v} [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hB : (⨆ i, B i) = ⊤) (T : Type u)
    [AddCommGroup T] [Module S T] (i : ι) (y : B i ⊗[S] T) :
    iSupColimTensorEquiv B hBmono hB T (Module.DirectLimit.of S ι (fun i => B i ⊗[S] T)
      (fun i j h => (iSupColimSystem B hBmono i j h).rTensor T) i y) =
      (Submodule.subtype (B i)).rTensor T y := by
  have key : (iSupColimTensorEquiv B hBmono hB T : _ →ₗ[S] _) ∘ₗ
      (Module.DirectLimit.of S ι (fun i => B i ⊗[S] T)
        (fun i j h => (iSupColimSystem B hBmono i j h).rTensor T) i)
      = (Submodule.subtype (B i)).rTensor T := by
    apply TensorProduct.ext'
    intro b t
    simp [iSupColimTensorEquiv, iSupColimEquiv_of, LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun key y

/-- **Union / filtered-colimit lemma.**  Let `A ⊆ Q` be submodules and let `B : ι → Submodule S Q` be a `Monotone` family (`i ≤ j → B i ≤ B j`) with `A ≤ B i` for all `i` and `⨆ i, B i = ⊤`.  If each inclusion `A ↪ B i` is `T`-pure, then so is `A ↪ Q`.  (The `Monotone` hypothesis is necessary: without it `⨆ i, B i` is the sum and not the filtered union.)

PLAN for the prover.  Let `z ∈ A ⊗[S] T` with image `0` in `Q ⊗[S] T`.  The tensor product commutes with the filtered colimit `Q = colim_i (B i)`, i.e. `Q ⊗[S] T = ⋃ i, range (B i ⊗[S] T → Q ⊗[S] T)`: `⊗` is a left adjoint, and concretely an element of `Q ⊗ T` is a finite sum `∑ q_j ⊗ t_j` with each `q_j` in some `B i_j`; by monotonicity and directedness all of them lie in a single `B i`, and the ranges are directed.  Hence `z`, which is `0` in `Q ⊗ T`, is `0` in some `B i ⊗[S] T`; since `A ↪ B i` is `T`-pure, `z = 0`.  (A clean way to package the commutation with filtered colimits is `TensorProduct`'s universal property: the map `Q × T → colim_i (B i ⊗[S] T)`, `(q,t) ↦ [q ⊗ t]` for any `i` with `q ∈ B i`, is well defined by monotonicity and bilinear, so it induces `Q ⊗ T → colim_i (B i ⊗ T)`, inverse to the canonical map.) -/
theorem tpure_of_iSup {S : Type _} [CommRing S] {Q : Type _} [AddCommGroup Q]
    [Module S Q] (A : Submodule S Q) {ι : Type _} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (B : ι → Submodule S Q) (hBmono : Monotone B) (hA : ∀ i, A ≤ B i)
    (hB : (⨆ i, B i) = ⊤) (T : Type _) [AddCommGroup T] [Module S T]
    (h : ∀ i, Work.DSFFP.TPure T (Submodule.inclusion (hA i))) :
    Work.DSFFP.TPure T A.subtype := by
  classical
  rw [TPure, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  obtain ⟨i0⟩ := ‹Nonempty ι›
  haveI hds : DirectedSystem (fun i => B i) (fun i j h => ⇑(iSupColimSystem B hBmono i j h)) :=
    iSupColimSystem_directedSystem B hBmono
  have hcomp : Submodule.subtype (B i0) ∘ₗ Submodule.inclusion (hA i0) = A.subtype := by
    ext x; rfl
  -- the class of `z` in `limᵢ (B i ⊗[S] T)` is `0`, because its image in `Q ⊗[S] T` is
  have h0 : iSupColimTensorEquiv B hBmono hB T
      (Module.DirectLimit.of S ι (fun i => B i ⊗[S] T)
        (fun i j h => (iSupColimSystem B hBmono i j h).rTensor T) i0
        ((Submodule.inclusion (hA i0)).rTensor T z)) = 0 := by
    rw [iSupColimTensorEquiv_of]
    have h1 : (Submodule.subtype (B i0)).rTensor T ∘ₗ (Submodule.inclusion (hA i0)).rTensor T
        = A.subtype.rTensor T := by
      rw [← LinearMap.rTensor_comp, hcomp]
    rw [← LinearMap.comp_apply, h1, hz]
  have hof : Module.DirectLimit.of S ι (fun i => B i ⊗[S] T)
      (fun i j h => (iSupColimSystem B hBmono i j h).rTensor T) i0
      ((Submodule.inclusion (hA i0)).rTensor T z) = 0 :=
    (iSupColimTensorEquiv B hBmono hB T).injective (by rw [h0, map_zero])
  -- hence `z` is killed "at some finite stage" `B j`
  obtain ⟨j, hij, hz'⟩ := Module.DirectLimit.of.zero_exact hof
  have hcomp2 : iSupColimSystem B hBmono i0 j hij ∘ₗ Submodule.inclusion (hA i0)
      = Submodule.inclusion (hA j) := by
    ext x; simp [iSupColimSystem, Submodule.inclusion_apply]
  have hz2 : (Submodule.inclusion (hA j)).rTensor T z = 0 := by
    rw [← hcomp2, LinearMap.rTensor_comp, LinearMap.comp_apply]
    exact hz'
  exact (h j) (by simpa using hz2)

end Work.DSFFP
