import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Q8.Vocab
import Submission.Work.BrauerSuzuki.Q8.GroupSetup
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The structural hypotheses of Glauberman's `Q₈` argument

`Work.BrauerSuzuki.Q8.Ctx x S` collects the conclusions of Glauberman (1974), step (1)
(`REFS/brauer_suzuki.md` §3, proved in `Q8/Cstar_Nstar_Astar` and `Q8/isTISet_cstar_diff`),
together with the elementary properties of the element `x` of order `4`:

* `X = ⟨x⟩`, `T = ⟨x²⟩`, `C* = C_G(X)`, `N* = N_G(X)`, `H* = O_{2'}(C*)`;
* `C* = X H* = X × H*` with `H*` of odd order;
* `N* = S H*`;
* `S ∩ C* = X`;
* `A* = C* \ T H*` is a TI set with normalizer `N*`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

/-- The structural hypotheses of Glauberman (1974) for the element `x` of order `4` in the
Sylow `2`-subgroup `S` of `G` (which is of `Q₈`-type). -/
structure Ctx (G : Type*) [Group G] [Finite G] (x : G) (S : Sylow 2 G) : Prop where
  hx4 : orderOf x = 4
  hxS : x ∈ (S : Subgroup G)
  card_S : Nat.card ↥(S : Subgroup G) = 8
  supC : X x ⊔ Hstar x = Cstar x
  infC : X x ⊓ Hstar x = ⊥
  comm : ∀ a ∈ X x, ∀ b ∈ Hstar x, a * b = b * a
  odd_H : Odd (Nat.card ↥(Hstar x))
  le_N : (S : Subgroup G) ≤ Nstar x
  supN : (S : Subgroup G) ⊔ Hstar x = Nstar x
  infSC : (S : Subgroup G) ⊓ Cstar x = X x
  isTI : Work.BrauerSuzuki.IsTISet (Astar x) (Nstar x)

namespace Ctx

variable {x : G} {S : Sylow 2 G}

theorem X_card (h : Ctx G x S) : Nat.card ↥(X x) = 4 := by
  rw [X, Nat.card_zpowers, h.hx4]

theorem X_le_Cstar (h : Ctx G x S) : X x ≤ Cstar x := by
  rw [← h.supC]; exact le_sup_left

theorem Hstar_le_Cstar (h : Ctx G x S) : Hstar x ≤ Cstar x := by
  rw [← h.supC]; exact le_sup_right

theorem Cstar_le_Nstar (h : Ctx G x S) : Cstar x ≤ Nstar x :=
  Subgroup.centralizer_le_normalizer (X x : Set G)

theorem X_le_Nstar (h : Ctx G x S) : X x ≤ Nstar x := h.X_le_Cstar.trans h.Cstar_le_Nstar

theorem Hstar_le_Nstar (h : Ctx G x S) : Hstar x ≤ Nstar x := h.Hstar_le_Cstar.trans h.Cstar_le_Nstar

theorem T_le_X (h : Ctx G x S) : T x ≤ X x := by
  rw [T, X]; exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)

theorem X_le_S (h : Ctx G x S) : X x ≤ (S : Subgroup G) := by
  rw [X]; exact Subgroup.zpowers_le.mpr h.hxS

theorem T_card (h : Ctx G x S) : Nat.card ↥(T x) = 2 := by
  have hx2 : orderOf (x ^ 2) = 2 := by
    have h2 : orderOf (x ^ 2) = orderOf x / Nat.gcd (orderOf x) 2 := orderOf_pow (n := 2) x
    rw [h.hx4] at h2
    rw [h2]; norm_num
  rw [T, Nat.card_zpowers, hx2]

theorem T_le_Cstar (h : Ctx G x S) : T x ≤ Cstar x := h.T_le_X.trans h.X_le_Cstar

theorem T_le_Nstar (h : Ctx G x S) : T x ≤ Nstar x := h.T_le_X.trans h.X_le_Nstar

/-- Conjugation by an element of `C*` preserves `H* = O_{2'}(C*)`. -/
theorem Hstar_conj (h : Ctx G x S) {c m : G} (hc : c ∈ Cstar x) (hm : m ∈ Hstar x) :
    c * m * c⁻¹ ∈ Hstar x := by
  rw [Hstar] at hm ⊢
  obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.mp hm
  have hwmval : (w : G) = m := hwm
  refine Subgroup.mem_map.mpr
    ⟨(⟨c, hc⟩ : ↥(Cstar x)) * w * (⟨c, hc⟩ : ↥(Cstar x))⁻¹, ?_, ?_⟩
  · exact (Work.BrauerSuzuki.oddCore_normal ↥(Cstar x)).conj_mem w hw (⟨c, hc⟩ : ↥(Cstar x))
  · simp [hwmval]

/-- Conjugation by an element of `N*` preserves `C* = C_G(X)`. -/
theorem Cstar_conj_Nstar (h : Ctx G x S) {n c : G} (hn : n ∈ Nstar x) (hc : c ∈ Cstar x) :
    n * c * n⁻¹ ∈ Cstar x := by
  rw [Cstar, Subgroup.mem_centralizer_iff] at hc ⊢
  intro a ha
  rw [Nstar, Subgroup.mem_normalizer_iff] at hn
  have hna : n⁻¹ * a * n ∈ X x := by
    have h2 : n * (n⁻¹ * a * n) * n⁻¹ ∈ X x := by
      have h3 : n * (n⁻¹ * a * n) * n⁻¹ = a := by group
      rw [h3]; exact ha
    exact (hn (n⁻¹ * a * n)).mpr h2
  calc a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hc (n⁻¹ * a * n) hna]
    _ = (n * c * n⁻¹) * a := by group

/-- The odd core is invariant under every group automorphism: it is the largest normal
odd-order subgroup, and both properties are preserved by isomorphisms. -/
theorem oddCore_map_mulEquiv {K : Type*} [Group K] [Finite K] (σ : K ≃* K) :
    Subgroup.map σ.toMonoidHom (Submission.Blueprint.oddCore K) =
      Submission.Blueprint.oddCore K := by
  refine le_antisymm ?_ ?_
  · exact Work.BrauerSuzuki.OddCore.le_of_normal_odd
      ((Work.BrauerSuzuki.oddCore_normal K).map σ.toMonoidHom σ.surjective)
      (by rw [Subgroup.card_map_of_injective σ.injective]
          exact Work.BrauerSuzuki.OddCore.oddCard_oddCore)
  · have h1 : Subgroup.map σ.symm.toMonoidHom (Submission.Blueprint.oddCore K) ≤
        Submission.Blueprint.oddCore K :=
      Work.BrauerSuzuki.OddCore.le_of_normal_odd
        ((Work.BrauerSuzuki.oddCore_normal K).map σ.symm.toMonoidHom σ.symm.surjective)
        (by rw [Subgroup.card_map_of_injective σ.symm.injective]
            exact Work.BrauerSuzuki.OddCore.oddCard_oddCore)
    calc Submission.Blueprint.oddCore K
        = Subgroup.map σ.toMonoidHom
            (Subgroup.map σ.symm.toMonoidHom (Submission.Blueprint.oddCore K)) := by
          rw [Subgroup.map_map,
            show σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id K from by ext; simp,
            Subgroup.map_id]
      _ ≤ Subgroup.map σ.toMonoidHom (Submission.Blueprint.oddCore K) := Subgroup.map_mono h1

/-- Conjugation by an element of `N*` preserves `H* = O_{2'}(C*)`. -/
theorem Hstar_conj_Nstar (h : Ctx G x S) {n m : G} (hn : n ∈ Nstar x) (hm : m ∈ Hstar x) :
    n * m * n⁻¹ ∈ Hstar x := by
  rw [Hstar] at hm ⊢
  obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.mp hm
  -- conjugation by `n` as an automorphism of `↥C*`
  let φ : ↥(Cstar x) →* ↥(Cstar x) :=
    ((MulAut.conj n).toMonoidHom.comp (Cstar x).subtype).codRestrict (Cstar x)
      (fun c => h.Cstar_conj_Nstar hn c.2)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (φ a : G) = (φ b : G) := congrArg Subtype.val hab
    simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply] at h1
    exact Subtype.ext ((MulAut.conj n).injective (by simpa [MulAut.conj_apply] using h1))
  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨⟨n⁻¹ * (y : G) * n, ?_⟩, ?_⟩
    · have h3 : n⁻¹ * (y : G) * n = n⁻¹ * (y : G) * (n⁻¹)⁻¹ := by group
      rw [h3]
      exact h.Cstar_conj_Nstar ((Nstar x).inv_mem hn) y.2
    · apply Subtype.ext
      show (MulAut.conj n) (n⁻¹ * (y : G) * n) = (y : G)
      rw [MulAut.conj_apply]
      group
  let σ : ↥(Cstar x) ≃* ↥(Cstar x) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hσ : σ w ∈ Submission.Blueprint.oddCore ↥(Cstar x) := by
    have hinv := oddCore_map_mulEquiv σ
    have : σ w ∈ Subgroup.map σ.toMonoidHom (Submission.Blueprint.oddCore ↥(Cstar x)) :=
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    rwa [hinv] at this
  refine Subgroup.mem_map.mpr ⟨σ w, hσ, ?_⟩
  have hσval : (φ w : G) = n * (w : G) * n⁻¹ := by
    show (MulAut.conj n) (w : G) = n * (w : G) * n⁻¹
    rw [MulAut.conj_apply]
  have hwmval : (w : G) = m := hwm
  show (φ w : G) = n * m * n⁻¹
  rw [hσval, hwmval]

/-- `H*` is normal in `N*`. -/
theorem Hstar_normal_Nstar (h : Ctx G x S) {n m : G} (hn : n ∈ Nstar x) (hm : m ∈ Hstar x) :
    n * m * n⁻¹ ∈ Hstar x := h.Hstar_conj_Nstar hn hm

/-- `H*` is normal in `C*`. -/
theorem Hstar_normal_Cstar (h : Ctx G x S) {n m : G} (hn : n ∈ Cstar x) (hm : m ∈ Hstar x) :
    n * m * n⁻¹ ∈ Hstar x := h.Hstar_conj hn hm

end Ctx

end Work.BrauerSuzuki.Q8
