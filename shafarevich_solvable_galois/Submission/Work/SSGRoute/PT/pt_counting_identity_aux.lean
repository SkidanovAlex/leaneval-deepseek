import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PT.pt_selmer_counting
import Submission.Work.SSGRoute.PT.pt_counting_assembly
import Submission.Work.SSGRoute.PT.pt_canonical_aux
import Submission.Work.SSGRoute.PT.pt_canonical_assembly
import Submission.Work.SSGRoute.PT.pt_reciprocal_set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `Work.SSGRoute.PT.pt_selmer_counting_identity`

This module holds the auxiliary lemmas that the *counting* lane
(`Submission/Work/SSGRoute/PT/pt_selmer_counting_identity.lean`) needs and that cannot be quoted
from `Submission/Work/SSGRoute/PT/pt_counting_identity_h1.lean` (that module imports the counting
lane's own file, so importing it back would be a cycle):

* `PT.natCard_annihilator_mul` — the pure linear-algebra half of the counting identity
  (`|W^⊥| · |W| = |P|` for a perfect pairing), and its additive form
  `PT.CountAux.natCard_annihilator_mul_additive`, which is the form in which the product of the
  local Tate pairings is available;
* `CountAux.primalClassSet_orthogonal_dualClassSet` — the *proved* reciprocity inclusion
  `V ⊆ W^⊥` at the level of the class sets (`primalClassSet`, `dualClassSet`), i.e. the
  representative-level reciprocity law `PT.pt_orthogonality_of_realizable` pushed through
  `PT.productFormFun_primalClassOf`.  It is the half of the middle exactness that *is* available;
  its converse `W^⊥ ⊆ V` is the arithmetic input of the counting identity (`G1⁺`'s clause (8)).

Everything here is stated in the vocabulary of `PT/pt_counting_assembly.lean` and
`PT/pt_canonical_assembly.lean` and rests on no unproved node.  (This module deliberately does
*not* import `PT/canonical_localPairing_reciprocity_converse.lean`: the `G1⁺` node is imported
only by the counting lane itself, so that everything above it can be built without it.)
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- **Cardinality form of the annihilator identity for a perfect pairing.**
For a pairing `β : P →ₗ Q →ₗ 𝔽_p` which is non-degenerate in both variables and a subspace
`W ≤ Q`, the "annotator" `{x : P // ∀ y ∈ W, β x y = 0}` of `W` satisfies
`|W^⊥| · |W| = |P|`.  This is the pure-linear-algebra half of the Poitou–Tate counting
identity. -/
theorem natCard_annihilator_mul {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p)
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y ∈ W, β x y = 0} * Nat.card W = Nat.card P := by
  classical
  haveI hPf : Module.Finite (ZMod p) P := Module.Finite.of_finite
  haveI hQf : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  haveI hWf : Module.Finite (ZMod p) W := Module.Finite.of_finite
  have hinjΦ : Function.Injective β := by
    intro x y hxy
    have hz : β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : Q, β (x - y) z = 0 := fun z => by rw [hz]; rfl
    have h1 : x - y = 0 := hndL (x - y) h0
    rwa [sub_eq_zero] at h1
  have hinjΨ : Function.Injective (LinearMap.flip β) := by
    intro x y hxy
    have hz : LinearMap.flip β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : P, β z (x - y) = 0 := by
      intro z
      have h1 := congrArg (fun (f : P →ₗ[ZMod p] ZMod p) => f z) hz
      simpa using h1
    have h1 : x - y = 0 := hndR (x - y) h0
    rwa [sub_eq_zero] at h1
  have hPQ : Module.finrank (ZMod p) P = Module.finrank (ZMod p) Q := by
    have h1 : Module.finrank (ZMod p) P ≤ Module.finrank (ZMod p) Q := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := P) (M' := Module.Dual (ZMod p) Q) hinjΦ
      rwa [Subspace.dual_finrank_eq] at h
    have h2 : Module.finrank (ZMod p) Q ≤ Module.finrank (ZMod p) P := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := Q) (M' := Module.Dual (ZMod p) P) hinjΨ
      rwa [Subspace.dual_finrank_eq] at h
    omega
  have hmem : ∀ x : P, (∀ y ∈ W, β x y = 0) ↔ x ∈ (Submodule.dualAnnihilator W).comap β := by
    intro x
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  have hann : Module.finrank (ZMod p) (Submodule.dualAnnihilator W)
      = Module.finrank (ZMod p) Q - Module.finrank (ZMod p) W := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  have hPQ' : Module.finrank (ZMod p) P = Module.finrank (ZMod p) (Module.Dual (ZMod p) Q) := by
    rw [Subspace.dual_finrank_eq]; exact hPQ
  have hcomap : Module.finrank (ZMod p) ((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) (Submodule.dualAnnihilator W) := by
    let f : ((Submodule.dualAnnihilator W).comap β) →ₗ[ZMod p]
        Submodule.dualAnnihilator W :=
      { toFun := fun x => ⟨β x.1, x.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp }
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        have h1 : β x.1 = β y.1 := congrArg Subtype.val hxy
        exact Subtype.ext (hinjΦ h1)
      · rintro ⟨φ, hφ⟩
        obtain ⟨x, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hPQ').mp
          hinjΦ φ
        exact ⟨⟨x, by rw [Submodule.mem_comap]; exact hφ⟩, Subtype.ext rfl⟩
    exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf)
  have hfin : Module.finrank (ZMod p) ↥((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) P - Module.finrank (ZMod p) W := by
    rw [hcomap, hann]; omega
  have hcard1 : Nat.card {x : P // ∀ y ∈ W, β x y = 0}
      = p ^ (Module.finrank (ZMod p) P - Module.finrank (ZMod p) W) := by
    have h1 : Nat.card {x : P // ∀ y ∈ W, β x y = 0}
        = Nat.card ↥((Submodule.dualAnnihilator W).comap β) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => hmem x))
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hfin]
  have hcard2 : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hcard3 : Nat.card P = p ^ Module.finrank (ZMod p) P := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hle : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) P := by
    have h1 : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) Q := Submodule.finrank_le W
    omega
  rw [hcard1, hcard2, hcard3, ← pow_add, Nat.sub_add_cancel hle]

namespace CountAux

set_option maxHeartbeats 1000000 in
/-- **Cardinality form of the annihilator identity for an additively given perfect pairing.**

`natCard_annihilator_mul` above is stated for a `ZMod p`-*bilinear* form; the product form of the
local Tate pairings (`Work.SSGRoute.PT.productFormFun`) is only known to be *additive* in each
variable (`productFormFun_add_left` / `productFormFun_add_right`).  Since the scalar action of
`ZMod p` on a `ZMod p`-module is determined by the additive structure, additivity in each variable
upgrades to bilinearity, and the counting lemma applies verbatim. -/
theorem natCard_annihilator_mul_additive {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (W : Submodule (ZMod p) Q) :
    Nat.card {x : P // ∀ y ∈ W, β x y = 0} * Nat.card W = Nat.card P := by
  classical
  have hzeroR : ∀ x : P, β x 0 = 0 := by
    intro x
    have h : β x 0 + β x 0 = β x 0 + 0 := by
      rw [← haddR x 0 0]; simp
    exact add_left_cancel h
  have hzeroL : ∀ y : Q, β 0 y = 0 := by
    intro y
    have h : β 0 y + β 0 y = β 0 y + 0 := by
      rw [← haddL 0 0 y]; simp
    exact add_left_cancel h
  have hnatL : ∀ (n : ℕ) (x : P) (y : Q), β (n • x) y = n • β x y := by
    intro n
    induction n with
    | zero => intro x y; rw [zero_nsmul, hzeroL, zero_nsmul]
    | succ n ih =>
      intro x y
      rw [succ_nsmul, haddL, ih x y, succ_nsmul]
  have hnatR : ∀ (n : ℕ) (x : P) (y : Q), β x (n • y) = n • β x y := by
    intro n
    induction n with
    | zero => intro x y; rw [zero_nsmul, hzeroR, zero_nsmul]
    | succ n ih =>
      intro x y
      rw [succ_nsmul, haddR, ih x y, succ_nsmul]
  have hsmulL : ∀ (c : ZMod p) (x : P) (y : Q), β (c • x) y = c * β x y := by
    intro c x y
    have h1 : β ((c.val : ZMod p) • x) y = (c.val : ZMod p) * β x y := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p), hnatL, nsmul_eq_mul]
    rwa [ZMod.natCast_zmod_val] at h1
  have hsmulR : ∀ (c : ZMod p) (x : P) (y : Q), β x (c • y) = c * β x y := by
    intro c x y
    have h1 : β x ((c.val : ZMod p) • y) = (c.val : ZMod p) * β x y := by
      rw [Nat.cast_smul_eq_nsmul (ZMod p), hnatR, nsmul_eq_mul]
    rwa [ZMod.natCast_zmod_val] at h1
  let f : P → Q →ₗ[ZMod p] ZMod p := fun x =>
    { toFun := β x
      map_add' := fun y y' => haddR x y y'
      map_smul' := fun c y => by
        show β x (c • y) = c • β x y
        rw [hsmulR c x y, smul_eq_mul] }
  let βlin : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p :=
    { toFun := f
      map_add' := fun x x' => by
        ext y
        show β (x + x') y = β x y + β x' y
        rw [haddL x x' y]
      map_smul' := fun c x => by
        ext y
        show β (c • x) y = c • β x y
        rw [hsmulL c x y, smul_eq_mul] }
  exact natCard_annihilator_mul (p := p) βlin hndL hndR W

end CountAux

end

open scoped TensorProduct Pointwise

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance instCountAuxDualAC :
    AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instCountAuxDualMod :
    Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
local instance instCountAuxDualDMA :
    DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance instCountAuxDualSMC :
    SMulCommClass (K ≃ₐ[k] K) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance

set_option maxHeartbeats 2000000 in
/-- **The reciprocity inclusion `V ⊆ W^⊥` at the level of the class sets.**

For local data `pair` satisfying the local axioms (1)–(5) at every place of `S ∪ C` and the
reciprocity law (7) `hrec`, every *realizable* class `x` (an element of `primalClassSet`) is
orthogonal, under the product form of the descended local pairings, to every relaxed dual Selmer
class `y` (an element of `dualClassSet`).

This is the representative-level reciprocity law
`Work.SSGRoute.PT.pt_orthogonality_of_realizable` (applied through
`Work.SSGRoute.PT.productFormFun_primalClassOf`, which identifies the class-level product form with
the sum of the local pairings on representatives).  The descended pairing is
`Work.SSGRoute.PT.localPairingFun pair hloc`, whose agreement with `pair` on locally constant
cocycles is `Work.SSGRoute.PT.localPairingFun_toClass`. -/
theorem CountAux.primalClassSet_orthogonal_dualClassSet
    (hKN : K ≤ N)
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 →
      ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair H)
    (hrec : Recip (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair) :
    ∀ x : primalClasses p k Ω K M S C,
      x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) →
      ∀ y : primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
        y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
            (S := S) (C := C) →
        productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
          (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
          x y = 0 := by
  classical
  intro x hx y hy
  rw [mem_primalClassSet_iff (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
    (M := M) (S := S) (C := C) hCinv x] at hx
  obtain ⟨α', β', ε, hcls, hε1, hε2, hεα', hεβ', hεunr⟩ := hx
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
  have hby : dualClassMap (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S)
      (C := C) b.1 = y := hb
  rw [← hby, ← hcls]
  have hεmem : ε ∈ primalSelmer p k Ω K N M S := ⟨hε1, hε2, hεunr⟩
  have hεα'lc : ∀ A ∈ S, (fun σ => ε σ - α' A σ) ∈
      lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    fun A hA => coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A)
      ((mem_coboundaries p k Ω K M (SSGRoute.decomp k A) _).mpr (hεα' A hA))
  have hεβ'lc : ∀ c ∈ C, (fun σ => ε σ - β' c σ) ∈
      lcCocycles p k Ω K M (Subgroup.zpowers c) :=
    fun c hc => coboundaries_le_lcCocycles p k Ω K M (Subgroup.zpowers c)
      ((mem_coboundaries p k Ω K M (Subgroup.zpowers c) _).mpr (hεβ' c hc))
  have hα'lc : ∀ A ∈ S, α' A ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) := by
    intro A hA
    have hεA : ε ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have heq : α' A = ε - (fun σ => ε σ - α' A σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεA (hεα'lc A hA)
  have hβ'lc : ∀ c ∈ C, β' c ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) := by
    intro c hc
    have hεc : ε ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) :=
      ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1, isLocConstOn_mono le_top hε2⟩
    have heq : β' c = ε - (fun σ => ε σ - β' c σ) := by
      ext σ; simp only [Pi.sub_apply]; abel
    rw [heq]
    exact Submodule.sub_mem _ hεc (hεβ'lc c hc)
  -- the descended pairing agrees with `pair` on locally constant cocycles
  have hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A) →
      localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
        (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b) = pair (SSGRoute.decomp k A) a b :=
    fun A hA => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inl ⟨A, hSfin A hA, rfl⟩)
  have hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) →
      b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c) →
      localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc
        (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b) = pair (Subgroup.zpowers c) a b :=
    fun c hc => localPairingFun_toClass (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc (Or.inr ⟨c, hCinv c hc, rfl⟩)
  obtain ⟨S', hS'sub, hS'fin, hS'disj, hS'good, hS'cob⟩ :=
    exists_reciprocal_set (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
      (T := T) (M := M) (S := S) hSfin hSdisj hSram ε hεmem b.1 b.2
  have hzero : ∑ A ∈ S, pair (SSGRoute.decomp k A) (α' A) b.1 +
      ∑ c ∈ C, pair (Subgroup.zpowers c) (β' c) b.1 = 0 :=
    pt_orthogonality_of_realizable (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      pair hloc hrec S hSfin C α' β' ε ⟨hε1, hε2⟩
      (fun A hA => hα'lc A hA) hεα' (fun A hA => hεα'lc A hA)
      (fun c hc => (hβ'lc c hc).1) hεβ' (fun c hc => hεβ'lc c hc)
      b.1 ⟨b.2.1, b.2.2.1⟩ S' hS'sub hS'fin hS'disj hS'good hS'cob hCinv hC hCdisj
  rw [productFormFun_primalClassOf (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T)
    (M := M) (S := S) (C := C) pair
    (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) pair hloc)
    hB hBc α' β' hα'lc hβ'lc b.1 b.2,
    Finset.sum_attach S (fun A => pair (SSGRoute.decomp k A) (α' A) b.1),
    Finset.sum_attach C (fun c => pair (Subgroup.zpowers c) (β' c) b.1)]
  exact hzero

end

end Work.SSGRoute.PT
