import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.exists_additive_coboundary
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.no_equivariant_linearEquiv
import Submission.Work.Higman.monomial_form
import Submission.Work.Higman.gcd_two_pow
import Submission.Work.Higman.orderOf_frobeniusEquiv_pow
import Submission.Work.Higman.exists_linearEquiv_monomial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman

/-! ## 1. The action of `ξ` on the two coordinates

For `P = TwoStep V W b` with `Z(P) = kerFst`, an automorphism `ξ` of `P` preserves the centre,
hence induces additive automorphisms `q2XiV` of `V` and `q2XiW` of `W` with
`ξ ⟨0,w⟩ = ⟨0, q2XiW w⟩` and `(ξ x).fst = q2XiV x.fst`. -/

section Action

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]

/-- An automorphism of a group maps the centre into the centre. -/
theorem q2_mulAut_mem_center {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  obtain ⟨y', rfl⟩ := φ.surjective y
  rw [← map_mul, ← map_mul, hz y']

variable [Finite V] [Finite W]
variable (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
variable (ξ : MulAut (TwoStep V W b))

include hcenter ξ

theorem q2_xi_mem_kerFst {x : TwoStep V W b} (hx : x ∈ TwoStep.kerFst) :
    ξ x ∈ TwoStep.kerFst := by
  rw [← hcenter]
  exact q2_mulAut_mem_center ξ (by rw [hcenter]; exact hx)

theorem q2_xi_fst_zero (w : W) : (ξ (⟨0, w⟩ : TwoStep V W b)).fst = 0 :=
  q2_xi_mem_kerFst hcenter ξ rfl

/-- `w ↦ (ξ ⟨0,w⟩).snd` is additive. -/
theorem q2_xiW_add (u v : W) :
    (ξ (⟨0, u + v⟩ : TwoStep V W b)).snd =
      (ξ (⟨0, u⟩ : TwoStep V W b)).snd + (ξ (⟨0, v⟩ : TwoStep V W b)).snd := by
  have h5 : (⟨0, u⟩ : TwoStep V W b) * ⟨0, v⟩ = ⟨0, u + v⟩ := by
    ext <;> simp [TwoStep.snd_mul, Biadd.zero_left]
  have h1 : ξ ((⟨0, u⟩ : TwoStep V W b) * ⟨0, v⟩) =
      ξ (⟨0, u⟩ : TwoStep V W b) * ξ (⟨0, v⟩ : TwoStep V W b) := map_mul ξ _ _
  have h2 := congrArg (fun x : TwoStep V W b => x.snd) h1
  rw [h5] at h2
  rw [TwoStep.snd_mul] at h2
  rw [q2_xi_fst_zero hcenter ξ u, q2_xi_fst_zero hcenter ξ v,
    Biadd.zero_left (b := b) (0 : V), add_zero] at h2
  exact h2

theorem q2_xiW_injective : Function.Injective (fun w : W => (ξ (⟨0, w⟩ : TwoStep V W b)).snd) := by
  intro u v huv
  have h : ξ (⟨0, u⟩ : TwoStep V W b) = ξ (⟨0, v⟩ : TwoStep V W b) := by
    ext
    · rw [q2_xi_fst_zero hcenter ξ, q2_xi_fst_zero hcenter ξ]
    · exact huv
  have h' : (⟨0, u⟩ : TwoStep V W b) = ⟨0, v⟩ := by
    simpa using congrArg (fun x => ξ⁻¹ x) h
  simpa using congrArg (fun x : TwoStep V W b => x.snd) h'

/-- **The automorphism of `W = Z(P)` induced by `ξ`.** -/
def q2XiW : W ≃+ W :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun w : W => (ξ (⟨0, w⟩ : TwoStep V W b)).snd) (q2_xiW_add hcenter ξ))
    ⟨q2_xiW_injective hcenter ξ, Finite.surjective_of_injective (q2_xiW_injective hcenter ξ)⟩

theorem q2XiW_apply (w : W) : q2XiW hcenter ξ w = (ξ (⟨0, w⟩ : TwoStep V W b)).snd := rfl

theorem q2_xi_apply_zero (w : W) :
    ξ (⟨0, w⟩ : TwoStep V W b) = ⟨0, q2XiW hcenter ξ w⟩ := by
  ext
  · exact q2_xi_fst_zero hcenter ξ w
  · rfl

/-- `v ↦ (ξ ⟨v,0⟩).fst` is additive. -/
theorem q2_xiV_add (u v : V) :
    (ξ (⟨u + v, 0⟩ : TwoStep V W b)).fst =
      (ξ (⟨u, 0⟩ : TwoStep V W b)).fst + (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := by
  have hzu : (⟨u, 0⟩ : TwoStep V W b) * ⟨v, 0⟩ =
      (⟨0, b u v⟩ : TwoStep V W b) * ⟨u + v, 0⟩ := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_left]
  have h1 : ξ ((⟨u, 0⟩ : TwoStep V W b) * ⟨v, 0⟩) =
      ξ (⟨u, 0⟩ : TwoStep V W b) * ξ (⟨v, 0⟩ : TwoStep V W b) := map_mul ξ _ _
  have h2 := congrArg (fun x : TwoStep V W b => x.fst) h1
  rw [TwoStep.fst_mul] at h2
  rw [hzu] at h2
  rw [map_mul] at h2
  rw [TwoStep.fst_mul] at h2
  rw [q2_xi_fst_zero hcenter ξ (b u v)] at h2
  rw [zero_add] at h2
  exact h2

theorem q2_xiV_injective : Function.Injective (fun v : V => (ξ (⟨v, 0⟩ : TwoStep V W b)).fst) := by
  intro u v huv
  have huv' : (ξ (⟨u, 0⟩ : TwoStep V W b)).fst = (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := huv
  have hx : ξ ((⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹) ∈ TwoStep.kerFst := by
    rw [map_mul, map_inv]
    rw [TwoStep.mem_kerFst]
    rw [TwoStep.fst_mul, TwoStep.fst_inv]
    rw [huv', AddExpTwo.add_self]
  have hxc : ξ ((⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹) ∈
      Subgroup.center (TwoStep V W b) := by rw [hcenter]; exact hx
  have hx' : (⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹ ∈ TwoStep.kerFst := by
    have h2 : (⟨u, 0⟩ : TwoStep V W b) * (⟨v, 0⟩ : TwoStep V W b)⁻¹ ∈
        Subgroup.center (TwoStep V W b) := by
      simpa using q2_mulAut_mem_center (ξ⁻¹) hxc
    rwa [hcenter] at h2
  rw [TwoStep.mem_kerFst] at hx'
  have huv'' : u + v = 0 := by simpa [TwoStep.fst_mul, TwoStep.fst_inv] using hx'
  calc u = u + 0 := by rw [add_zero]
    _ = u + (v + v) := by rw [AddExpTwo.add_self]
    _ = (u + v) + v := by abel
    _ = v := by rw [huv'', zero_add]

/-- **The automorphism of `V = P/Z(P)` induced by `ξ`.** -/
def q2XiV : V ≃+ V :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun v : V => (ξ (⟨v, 0⟩ : TwoStep V W b)).fst) (q2_xiV_add hcenter ξ))
    ⟨q2_xiV_injective hcenter ξ, Finite.surjective_of_injective (q2_xiV_injective hcenter ξ)⟩

theorem q2XiV_apply (v : V) : q2XiV hcenter ξ v = (ξ (⟨v, 0⟩ : TwoStep V W b)).fst := rfl

theorem q2_xi_fst (x : TwoStep V W b) : (ξ x).fst = q2XiV hcenter ξ x.fst := by
  have hx : (⟨x.fst, 0⟩ : TwoStep V W b) * ⟨0, x.snd⟩ = x := by
    ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right, Biadd.zero_left]
  have h1 : ξ x = ξ (⟨x.fst, 0⟩ : TwoStep V W b) * ξ (⟨0, x.snd⟩ : TwoStep V W b) := by
    rw [← map_mul, hx]
  rw [h1, TwoStep.fst_mul, q2_xi_fst_zero hcenter ξ x.snd, add_zero]
  rfl

/-- **`ξ`-equivariance of the squaring form** `u ↦ b u u`. -/
theorem q2_xiV_quad (u : V) :
    b (q2XiV hcenter ξ u) (q2XiV hcenter ξ u) = q2XiW hcenter ξ (b u u) := by
  have h1 : (ξ (⟨u, 0⟩ : TwoStep V W b)) ^ 2 =
      (⟨0, b (q2XiV hcenter ξ u) (q2XiV hcenter ξ u)⟩ : TwoStep V W b) := by
    rw [TwoStep.sq_eq]
    rfl
  have h2 : (ξ (⟨u, 0⟩ : TwoStep V W b)) ^ 2 =
      (⟨0, q2XiW hcenter ξ (b u u)⟩ : TwoStep V W b) := by
    rw [← map_pow, TwoStep.sq_eq]
    exact q2_xi_apply_zero hcenter ξ (b u u)
  exact congrArg (fun x : TwoStep V W b => x.snd) (h1.symm.trans h2)

end Action

/-! ## 1b. The induced automorphisms as linear maps, and their powers -/

section Linear

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]
variable [Finite V] [Finite W] [Module (ZMod 2) V] [Module (ZMod 2) W]
variable (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
variable (ξ : MulAut (TwoStep V W b))

include hcenter ξ

theorem q2XiV_smul (r : ZMod 2) (v : V) : q2XiV hcenter ξ (r • v) = r • q2XiV hcenter ξ v := by
  have h : r = 0 ∨ r = 1 := by revert r; decide
  rcases h with h | h <;> simp [h]

theorem q2XiW_smul (r : ZMod 2) (w : W) : q2XiW hcenter ξ (r • w) = r • q2XiW hcenter ξ w := by
  have h : r = 0 ∨ r = 1 := by revert r; decide
  rcases h with h | h <;> simp [h]

/-- `ξ` on `V = P/Z(P)`, as a linear map. -/
def q2Tau : V ≃ₗ[ZMod 2] V := AddEquiv.toLinearEquiv (q2XiV hcenter ξ) (q2XiV_smul hcenter ξ)

/-- `ξ` on `W = Z(P)`, as a linear map. -/
def q2Sig : W ≃ₗ[ZMod 2] W := AddEquiv.toLinearEquiv (q2XiW hcenter ξ) (q2XiW_smul hcenter ξ)

theorem q2Tau_apply (v : V) : q2Tau hcenter ξ v = q2XiV hcenter ξ v := rfl

theorem q2Sig_apply (w : W) : q2Sig hcenter ξ w = q2XiW hcenter ξ w := rfl

theorem q2Tau_quad (u : V) :
    b (q2Tau hcenter ξ u) (q2Tau hcenter ξ u) = q2Sig hcenter ξ (b u u) :=
  q2_xiV_quad hcenter ξ u

theorem q2_xi_pow_apply_zero : ∀ (k : ℕ) (w : W),
    (ξ ^ k) (⟨0, w⟩ : TwoStep V W b) = ⟨0, (q2Sig hcenter ξ ^ k) w⟩ := by
  intro k
  induction k with
  | zero => intro w; rfl
  | succ k ih =>
      intro w
      rw [pow_succ, pow_succ, MulAut.mul_apply, q2_xi_apply_zero hcenter ξ,
        LinearEquiv.mul_apply, q2Sig_apply, ih]

end Linear

/-! ## 2. Helper: in an exponent-two group, `a + b = c` gives `a = c + b` -/

theorem q2_eq_add_of_add_eq {Z : Type*} [AddCommGroup Z] [AddExpTwo Z] {a b c : Z}
    (h : a + b = c) : a = c + b := by
  have h1 : a + c = b := calc a + c = a + (a + b) := by rw [h]
    _ = (a + a) + b := by abel
    _ = b := by rw [AddExpTwo.add_self, zero_add]
  calc a = a + 0 := by rw [add_zero]
    _ = a + (c + c) := by rw [AddExpTwo.add_self]
    _ = (a + c) + c := by abel
    _ = b + c := by rw [h1]
    _ = c + b := by rw [add_comm]

/-- The polar identity for a biadditive form: `b (u+v) (u+v) + b u u + b v v = b u v + b v u`. -/
theorem q2_b_polar {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b] (u v : V) :
    b (u + v) (u + v) + b u u + b v v = b u v + b v u := by
  have h1 : b (u + v) (u + v) = b u u + b u v + b v u + b v v := by
    rw [Biadd.add_left (b := b) u v (u + v), Biadd.add_right (b := b) u u v,
      Biadd.add_right (b := b) v u v]
    abel
  rw [h1]
  have h2 : b u u + b u v + b v u + b v v + b u u + b v v =
      (b u u + b u u) + (b v v + b v v) + (b u v + b v u) := by abel
  rw [h2, AddExpTwo.add_self (b u u), AddExpTwo.add_self (b v v), zero_add, zero_add]

/-! ## 3. Orbit counting for a linear automorphism of an `𝔽₂`-space -/

theorem q2_orderOf_of_transitive_linear {V : Type} [AddCommGroup V] [AddExpTwo V] [Finite V]
    [Module (ZMod 2) V] (τ : V ≃ₗ[ZMod 2] V) (hV : 2 ≤ Nat.card V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (τ ^ k) a = b) :
    orderOf τ = Nat.card V - 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun v => by simpa using congrFun h v))
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra h
    push_neg at h
    haveI : Subsingleton V := ⟨fun a b => by rw [h a, h b]⟩
    have h1 : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => Subsingleton.elim a b)
    rw [Nat.card_eq_fintype_card] at hV
    omega
  have hfixz : ∀ (i : ℤ), (τ ^ i) w0 = w0 → (τ ^ i) = 1 := by
    intro i hi
    ext v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · obtain ⟨j, hj⟩ := htrans w0 v hw0 hv
      have hj' : (τ ^ (j : ℤ)) w0 = v := by simpa using hj
      calc (τ ^ i) v = (τ ^ i) ((τ ^ (j : ℤ)) w0) := by rw [hj']
        _ = (τ ^ (i + j)) w0 := by rw [← LinearEquiv.mul_apply, ← zpow_add]
        _ = (τ ^ (j + i)) w0 := by rw [add_comm]
        _ = (τ ^ (j : ℤ)) ((τ ^ i) w0) := by rw [← LinearEquiv.mul_apply, ← zpow_add]
        _ = (τ ^ (j : ℤ)) w0 := by rw [hi]
        _ = v := hj'
  have hstab_bot : MulAction.stabilizer (Subgroup.zpowers τ) w0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hgw : (g : V ≃ₗ[ZMod 2] V) w0 = w0 := ‹g ∈ MulAction.stabilizer (Subgroup.zpowers τ) w0›
    have hgi : (τ ^ i) = 1 := by
      apply hfixz
      rw [hi]
      exact hgw
    exact Subtype.ext (by rw [← hi, hgi]; rfl)
  have horb : (MulAction.orbit (Subgroup.zpowers τ) w0 : Set V) = {v | v ≠ 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      intro hv
      apply hw0
      have hg : (g : V ≃ₗ[ZMod 2] V) w0 = (0 : V) := hv
      have h2 := congrArg (fun x => (g : V ≃ₗ[ZMod 2] V).symm x) hg
      simpa using h2
    · intro hv
      obtain ⟨j, hj⟩ := htrans w0 v hw0 hv
      exact ⟨⟨τ ^ j, Subgroup.pow_mem (Subgroup.zpowers τ) (Subgroup.mem_zpowers τ) j⟩, hj⟩
  have horbcard : Nat.card (MulAction.orbit (Subgroup.zpowers τ) w0) = Nat.card V - 1 := by
    rw [Nat.card_coe_set_eq, horb]
    exact card_subtype_ne_zero V 0
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers τ) w0)
  rw [Nat.card_prod, Nat.card_zpowers, hstab_bot, Subgroup.card_bot, mul_one] at hos
  rw [horbcard] at hos
  exact hos.symm

/-- If no non-trivial power of `τ` fixes a non-zero vector, then `τ` is transitive on the
non-zero vectors. -/
theorem q2_transitive_of_free_linear {V : Type} [AddCommGroup V] [AddExpTwo V] [Finite V]
    [Module (ZMod 2) V] (τ : V ≃ₗ[ZMod 2] V)
    (h : ∀ k : ℕ, 0 < k → k < Nat.card V - 1 → ∀ u : V, u ≠ 0 → (τ ^ k) u ≠ u) :
    ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (τ ^ k) a = b := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun v => by simpa using congrFun h v))
  intro a b ha hb
  have hex : ∃ d : ℕ, 0 < d ∧ (τ ^ d) a = a :=
    ⟨orderOf τ, orderOf_pos_iff.mpr (by simpa using isOfFinOrder_of_finite τ),
      by rw [pow_orderOf_eq_one]; rfl⟩
  obtain ⟨d, hdpos, hdfix, hdmin⟩ : ∃ d : ℕ, 0 < d ∧ (τ ^ d) a = a ∧
      ∀ e : ℕ, 0 < e → (τ ^ e) a = a → d ≤ e :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun e he hf => Nat.find_min' hex ⟨he, hf⟩⟩
  have hdle : Nat.card V - 1 ≤ d := by
    by_contra hlt
    push_neg at hlt
    exact h d hdpos hlt a ha hdfix
  have hinj : Function.Injective (fun i : Fin d => (τ ^ (i : ℕ)) a) := by
    intro i j hij
    change (τ ^ (i : ℕ)) a = (τ ^ (j : ℕ)) a at hij
    have hilt : (i : ℕ) < d := i.isLt
    have hjlt : (j : ℕ) < d := j.isLt
    rcases le_total (i : ℕ) j with hle | hle
    · have h2 : (τ ^ (i : ℕ)) ((τ ^ ((j : ℕ) - (i : ℕ))) a) = (τ ^ (j : ℕ)) a := by
        rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
      have h3 : (τ ^ ((j : ℕ) - (i : ℕ))) a = a :=
        (τ ^ (i : ℕ)).injective (by rw [h2, hij])
      rcases Nat.eq_zero_or_pos ((j : ℕ) - (i : ℕ)) with h0 | hpos
      · exact Fin.ext (by omega)
      · exact absurd (hdmin _ hpos h3) (by omega)
    · have h2 : (τ ^ (j : ℕ)) ((τ ^ ((i : ℕ) - (j : ℕ))) a) = (τ ^ (i : ℕ)) a := by
        rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
      have h3 : (τ ^ ((i : ℕ) - (j : ℕ))) a = a :=
        (τ ^ (j : ℕ)).injective (by rw [h2, hij])
      rcases Nat.eq_zero_or_pos ((i : ℕ) - (j : ℕ)) with h0 | hpos
      · exact Fin.ext (by omega)
      · exact absurd (hdmin _ hpos h3) (by omega)
  have himg : Set.range (fun i : Fin d => (τ ^ (i : ℕ)) a) ⊆
      MulAction.orbit (Subgroup.zpowers τ) a := by
    rintro _ ⟨i, rfl⟩
    rw [MulAction.mem_orbit_iff]
    exact ⟨⟨τ ^ (i : ℕ), Subgroup.pow_mem (Subgroup.zpowers τ) (Subgroup.mem_zpowers τ) _⟩, rfl⟩
  have hOsub : MulAction.orbit (Subgroup.zpowers τ) a ⊆ {v : V | v ≠ 0} := by
    rintro _ ⟨g, rfl⟩ h0
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have h1 : (τ ^ i) a = 0 := by rw [hi]; exact h0
    have h3 := congrArg (fun x => (τ ^ i).symm x) h1
    rw [LinearEquiv.symm_apply_apply, map_zero] at h3
    exact ha h3
  have hncardO : Nat.card V - 1 ≤ (MulAction.orbit (Subgroup.zpowers τ) a).ncard := by
    calc Nat.card V - 1 ≤ d := hdle
      _ = (Set.range (fun i : Fin d => (τ ^ (i : ℕ)) a)).ncard := by
            rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
      _ ≤ (MulAction.orbit (Subgroup.zpowers τ) a).ncard :=
            Set.ncard_le_ncard himg (Set.toFinite _)
  have hncardS : ({v : V | v ≠ 0} : Set V).ncard = Nat.card V - 1 := by
    rw [← Nat.card_coe_set_eq]
    exact card_subtype_ne_zero V 0
  have hOeq : MulAction.orbit (Subgroup.zpowers τ) a = {v : V | v ≠ 0} := by
    refine Set.eq_of_subset_of_ncard_le hOsub ?_
    rw [hncardS]
    exact hncardO
  have hbO : b ∈ MulAction.orbit (Subgroup.zpowers τ) a := by rw [hOeq]; exact hb
  rw [MulAction.mem_orbit_iff] at hbO
  obtain ⟨g, hg⟩ := hbO
  obtain ⟨k, hk⟩ : ∃ k : ℕ, τ ^ k = (g : V ≃ₗ[ZMod 2] V) := by
    have h2 := (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_finite τ)).mp g.2
    rcases Finset.mem_image.mp h2 with ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  exact ⟨k, by rw [hk]; exact hg⟩

/-! ## 4. The monomial normal form (Higman's Lemma 11, algebraic core) -/

theorem q2_monomial_normal_form {n : ℕ} (hn : 0 < n)
    (ν lam : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    (hnotconj : ∀ s : ℕ, (ν : GaloisField 2 n) ≠ (lam : GaloisField 2 n) ^ 2 ^ s)
    (Q : GaloisField 2 n → GaloisField 2 n) (hQ0 : Q 0 = 0)
    (hQne : ∀ α : GaloisField 2 n, α ≠ 0 → Q α ≠ 0)
    (hadd1 : ∀ α α' γ : GaloisField 2 n,
      Q (α + α' + γ) + Q (α + α') + Q γ =
        (Q (α + γ) + Q α + Q γ) + (Q (α' + γ) + Q α' + Q γ))
    (hadd2 : ∀ α γ γ' : GaloisField 2 n,
      Q (α + (γ + γ')) + Q α + Q (γ + γ') =
        (Q (α + γ) + Q α + Q γ) + (Q (α + γ') + Q α + Q γ'))
    (hξ : ∀ α : GaloisField 2 n, Q ((ν : GaloisField 2 n) * α) = (lam : GaloisField 2 n) * Q α) :
    ∃ (φ : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n),
      θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
      ∀ α, Q α = (φ α) * θ (φ α) := by
  obtain ⟨i, j, hij, hjn, hνlam, c, hc, hQ⟩ :=
    monomial_form hn ν lam hν hlam hnotconj Q hQ0 hQne hadd1 hadd2 hξ
  have hdpos : 0 < j - i := by omega
  have h2d : 2 ^ i * (1 + 2 ^ (j - i)) = 2 ^ i + 2 ^ j := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' (le_of_lt hij)]
  -- the coprimality, from `ν ^ (2^i + 2^j) = lam`
  have hgcd : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) = 1 := by
    have hνlam' : ν ^ (2 ^ i + 2 ^ j) = lam := Units.ext hνlam
    have hord : orderOf (ν ^ (2 ^ i + 2 ^ j)) = 2 ^ n - 1 := by rw [hνlam']; exact hlam
    have h := orderOf_pow (x := ν) (n := 2 ^ i + 2 ^ j)
    rw [hν, hord] at h
    have hpos : 0 < 2 ^ n - 1 := by
      have : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by norm_num)
      omega
    have hgdvd : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) ∣ (2 ^ n - 1) := Nat.gcd_dvd_left _ _
    have h5 : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) * (2 ^ n - 1) = (2 ^ n - 1) := by
      have h4 : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) *
          ((2 ^ n - 1) / (2 ^ n - 1).gcd (2 ^ i + 2 ^ j)) = (2 ^ n - 1) :=
        Nat.mul_div_cancel' hgdvd
      rwa [← h] at h4
    have h6 : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) * (2 ^ n - 1) = 1 * (2 ^ n - 1) := by
      rw [one_mul]; exact h5
    exact Nat.mul_right_cancel hpos h6
  have hcop : Nat.Coprime (2 ^ (j - i) + 1) (2 ^ n - 1) := by
    have hm0 : (2 ^ i + 2 ^ j).Coprime (2 ^ n - 1) := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact hgcd
    have hm : (2 ^ n - 1).Coprime (2 ^ i + 2 ^ j) := hm0.symm
    rw [← h2d] at hm
    have h3 : (2 ^ n - 1).Coprime (1 + 2 ^ (j - i)) :=
      hm.coprime_dvd_right (dvd_mul_left _ _)
    have h3' : (1 + 2 ^ (j - i)).Coprime (2 ^ n - 1) := h3.symm
    have h4 : (2 ^ (j - i) + 1).Coprime (2 ^ n - 1) := by
      rw [add_comm]
      exact h3'
    exact h4
  -- `θ = Frobenius ^ (j - i)`
  let θ : GaloisField 2 n ≃+* GaloisField 2 n := (frobeniusEquiv (GaloisField 2 n) 2) ^ (j - i)
  have hθord : orderOf θ = n / n.gcd (j - i) := orderOf_frobeniusEquiv_pow n (j - i) hn
  have hθodd : Odd (orderOf θ) := by
    rw [hθord]
    exact (gcd_two_pow n (j - i) hn).mp hcop.symm.gcd_eq_one
  have hθne : θ ≠ RingEquiv.refl _ := by
    intro heq
    have h1 : orderOf θ = 1 := by rw [heq]; exact orderOf_one
    rw [hθord] at h1
    have hgdvd : n.gcd (j - i) ∣ n := Nat.gcd_dvd_left _ _
    have h2 : n = n.gcd (j - i) := by
      have h3 : n = n.gcd (j - i) * (n / n.gcd (j - i)) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel hgdvd).symm
      nth_rewrite 1 [h3]
      rw [h1, mul_one]
    have h3 : n ∣ j - i := by rw [h2]; exact Nat.gcd_dvd_right _ _
    have h4 : 0 < j - i := by omega
    have h5 : n ≤ j - i := Nat.le_of_dvd h4 h3
    omega
  have hθpow : ∀ β : GaloisField 2 n, θ β = β ^ 2 ^ (j - i) := by
    intro β
    show ((frobeniusEquiv (GaloisField 2 n) 2) ^ (j - i)) β = β ^ 2 ^ (j - i)
    induction j - i with
    | zero => simp
    | succ k ih =>
        rw [pow_succ']
        show (frobeniusEquiv (GaloisField 2 n) 2) (((frobeniusEquiv (GaloisField 2 n) 2) ^ k) β) =
          β ^ 2 ^ (k + 1)
        have h3 : (frobeniusEquiv (GaloisField 2 n) 2) (β ^ 2 ^ k) = (β ^ 2 ^ k) ^ 2 :=
          frobeniusEquiv_def (p := 2) (x := β ^ 2 ^ k)
        rw [ih, h3, ← pow_mul, ← pow_succ]
  obtain ⟨φ, hφ⟩ := exists_linearEquiv_monomial hij hjn hcop c hc Q hQ
  refine ⟨φ, θ, hθne, hθodd, fun α => ?_⟩
  rw [hφ α, hθpow, pow_add, pow_one]

/-! ## 5. The Singer cycles are not Frobenius conjugate -/

/-- Multiplication by a unit of `GF(2^n)` as an `𝔽₂`-linear automorphism. -/
def q2MulLin {n : ℕ} (u : (GaloisField 2 n)ˣ) : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n :=
  AddEquiv.toLinearEquiv
    { toFun := fun x => (u : GaloisField 2 n) * x
      invFun := fun x => ((u⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x
      left_inv := fun x => by
        show ((u⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * ((u : GaloisField 2 n) * x) = x
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      right_inv := fun x => by
        show (u : GaloisField 2 n) * (((u⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x) = x
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      map_add' := fun x y => by rw [mul_add] }
    (fun r x => by
      have h : r = 0 ∨ r = 1 := by revert r; decide
      rcases h with h | h <;> simp [h])

theorem q2MulLin_apply {n : ℕ} (u : (GaloisField 2 n)ˣ) (x : GaloisField 2 n) :
    q2MulLin u x = (u : GaloisField 2 n) * x := rfl

/-- The `𝔽₂`-linear automorphism `x ↦ x ^ (2 ^ t)` of `GF(2^n)`. -/
def q2FrobLin (n t : ℕ) : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n :=
  AddEquiv.toLinearEquiv
    ((frobeniusEquiv (GaloisField 2 n) 2 ^ t : GaloisField 2 n ≃+* GaloisField 2 n).toAddEquiv)
    (fun r x => by
      have h : r = 0 ∨ r = 1 := by revert r; decide
      rcases h with h | h <;> simp [h])

theorem q2FrobLin_apply (n t : ℕ) (x : GaloisField 2 n) :
    q2FrobLin n t x = x ^ 2 ^ t := by
  show ((frobeniusEquiv (GaloisField 2 n) 2 ^ t).toAddEquiv) x = x ^ 2 ^ t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ']
      show (frobeniusEquiv (GaloisField 2 n) 2)
        (((frobeniusEquiv (GaloisField 2 n) 2) ^ t).toAddEquiv x) = x ^ 2 ^ (t + 1)
      have h3 : (frobeniusEquiv (GaloisField 2 n) 2)
          (((frobeniusEquiv (GaloisField 2 n) 2) ^ t).toAddEquiv x) =
          (((frobeniusEquiv (GaloisField 2 n) 2) ^ t).toAddEquiv x) ^ 2 :=
        frobeniusEquiv_def (p := 2) (x := ((frobeniusEquiv (GaloisField 2 n) 2) ^ t).toAddEquiv x)
      rw [h3, ih, ← pow_mul, ← pow_succ]

theorem q2_field_not_conj (n : ℕ) (hn : 0 < n)
    (ν lam : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    (β : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n)
    (h1 : ∀ a b d : GaloisField 2 n, β (a + b) d = β a d + β b d)
    (h2 : ∀ a b d : GaloisField 2 n, β a (b + d) = β a b + β a d)
    (halt : ∀ a : GaloisField 2 n, β a a = 0)
    (heq : ∀ a b : GaloisField 2 n,
      β ((ν : GaloisField 2 n) * a) ((ν : GaloisField 2 n) * b) =
        (lam : GaloisField 2 n) * β a b)
    (hne : ∃ a b : GaloisField 2 n, β a b ≠ 0) :
    ∀ s : ℕ, (ν : GaloisField 2 n) ≠ (lam : GaloisField 2 n) ^ 2 ^ s := by
  classical
  have hcardU : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn.ne']
  have hνsurj : ∀ u : (GaloisField 2 n)ˣ, ∃ k : ℕ, ν ^ k = u := by
    intro u
    have htop : Subgroup.zpowers ν = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hν, hcardU]
    have hu : u ∈ Subgroup.zpowers ν := by rw [htop]; exact Subgroup.mem_top u
    have hfin : IsOfFinOrder ν := isOfFinOrder_of_finite ν
    obtain ⟨k, -, hk⟩ :=
      Finset.mem_image.mp ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp hu)
    exact ⟨k, hk⟩
  have hmulpow : ∀ (k : ℕ) (x : GaloisField 2 n),
      (q2MulLin ν ^ k) x = (ν : GaloisField 2 n) ^ k * x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', LinearEquiv.mul_apply, ih, q2MulLin_apply, pow_succ', mul_assoc]
  have hνtrans : ∀ a d : GaloisField 2 n, a ≠ 0 → d ≠ 0 →
      ∃ k : ℕ, ((q2MulLin ν) ^ k) a = d := by
    intro a d ha hd
    obtain ⟨k, hk⟩ := hνsurj (Units.mk0 d hd * (Units.mk0 a ha)⁻¹)
    refine ⟨k, ?_⟩
    rw [hmulpow k a]
    have hkc : ((ν ^ k : (GaloisField 2 n)ˣ) : GaloisField 2 n) =
        ((Units.mk0 d hd * (Units.mk0 a ha)⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) :=
      congrArg (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n)) hk
    rw [← Units.val_pow_eq_pow_val, hkc, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, Units.val_mk0, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  have hno : ¬ ∃ σ : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n,
      ∀ v : GaloisField 2 n, σ (q2MulLin ν v) = q2MulLin lam (σ v) :=
    no_equivariant_linearEquiv (q2MulLin ν) hνtrans (q2MulLin lam) β h1 h2 halt heq hne
  intro s hs
  obtain ⟨q, r, hr, hsr⟩ : ∃ q r : ℕ, r < n ∧ s = q * n + r :=
    ⟨s / n, s % n, Nat.mod_lt _ hn, by rw [mul_comm]; exact (Nat.div_add_mod s n).symm⟩
  have hpow : 2 ^ s = (2 ^ n) ^ q * 2 ^ r := by rw [hsr, pow_add, mul_comm q n, pow_mul]
  have hlam_n : (lam : GaloisField 2 n) ^ 2 ^ n = (lam : GaloisField 2 n) := by
    have h1' : orderOf (lam : GaloisField 2 n) = 2 ^ n - 1 := by
      rw [orderOf_units]; exact hlam
    have h2' : (lam : GaloisField 2 n) ^ (2 ^ n - 1) = 1 := by
      rw [← h1']; exact pow_orderOf_eq_one _
    calc (lam : GaloisField 2 n) ^ 2 ^ n
        = (lam : GaloisField 2 n) ^ ((2 ^ n - 1) + 1) := by
          rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]
      _ = (lam : GaloisField 2 n) ^ (2 ^ n - 1) * (lam : GaloisField 2 n) := by
          rw [pow_add, pow_one]
      _ = (lam : GaloisField 2 n) := by rw [h2', one_mul]
  have hlam_q : ∀ q : ℕ, (lam : GaloisField 2 n) ^ (2 ^ n) ^ q = (lam : GaloisField 2 n) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have h2 : ((2 : ℕ) ^ n) ^ (q + 1) = ((2 : ℕ) ^ n) ^ q * (2 : ℕ) ^ n :=
          pow_succ _ _
        rw [h2, pow_mul, ih, hlam_n]
  have hνr : (ν : GaloisField 2 n) = (lam : GaloisField 2 n) ^ 2 ^ r := by
    rw [hs, hpow, pow_mul, hlam_q q]
  have hνlam : (ν : GaloisField 2 n) ^ 2 ^ (n - r) = (lam : GaloisField 2 n) := by
    rw [hνr, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_of_lt hr)]
    exact hlam_n
  exact hno ⟨q2FrobLin n (n - r), fun x => by
    show (q2FrobLin n (n - r)) (q2MulLin ν x) = q2MulLin lam ((q2FrobLin n (n - r)) x)
    rw [q2MulLin_apply ν, q2MulLin_apply lam, q2FrobLin_apply, q2FrobLin_apply, mul_pow, hνlam]⟩

/-! ## 6. The target -/

theorem twoStep_q2_normal_form
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W)
    (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ (n : ℕ) (φ : V ≃+ GaloisField 2 n) (ψ : W ≃+ GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (c : GaloisField 2 n → GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
      ∀ u v : V, ψ (b u v) = aCocycle (GaloisField 2 n) θ (φ u) (φ v) +
        (c (φ u) + c (φ v) + c (φ u + φ v)) := by
  classical
  haveI : Finite W := finite_of_hW hW
  haveI : Finite V := (Nat.card_ne_zero.mp (by rw [hcardV]; omega)).2
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule (fun x => by rw [two_nsmul]; exact AddExpTwo.add_self x)
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule (fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z)
  -- ## cardinalities
  obtain ⟨n, hnW⟩ : ∃ n : ℕ, Nat.card W = 2 ^ n := card_W_eq_two_pow hW
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hnW
      simp at hnW
      omega
    · exact h
  have hVn : Nat.card V = 2 ^ n := by rw [hcardV, hnW]
  have hn2 : 2 ≤ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := by rw [← hnW]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  -- ## `ξ` acts transitively on the non-zero elements of `W`
  have hσtrans : ∀ a d : W, a ≠ 0 → d ≠ 0 → ∃ k : ℕ, (q2Sig hcenter ξ ^ k) a = d := by
    intro a d ha hd
    obtain ⟨k, hk⟩ := htrans (⟨0, a⟩ : TwoStep V W b) ⟨0, d⟩
      ((orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, ha⟩)
      ((orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, hd⟩)
    refine ⟨k, ?_⟩
    have h1 := q2_xi_pow_apply_zero hcenter ξ k a
    have h2 : (⟨0, (q2Sig hcenter ξ ^ k) a⟩ : TwoStep V W b) = ⟨0, d⟩ := by
      rw [← h1]; exact hk
    simpa using congrArg (fun x : TwoStep V W b => x.snd) h2
  have hσord : orderOf (q2Sig hcenter ξ) = Nat.card W - 1 :=
    q2_orderOf_of_transitive_linear (q2Sig hcenter ξ) (by omega) hσtrans
  -- ## a non-zero fixed point of a power of `σ` forces that power to be trivial
  have hσ_fixed_one : ∀ (k : ℕ) (w : W), w ≠ 0 → (q2Sig hcenter ξ ^ k) w = w →
      (q2Sig hcenter ξ ^ k) = 1 := by
    intro k w hw hfix
    ext w'
    rcases eq_or_ne w' 0 with rfl | hw'
    · simp
    · obtain ⟨j, hj⟩ := hσtrans w w' hw hw'
      calc (q2Sig hcenter ξ ^ k) w' = (q2Sig hcenter ξ ^ k) ((q2Sig hcenter ξ ^ j) w) := by rw [hj]
        _ = (q2Sig hcenter ξ ^ (k + j)) w := by rw [pow_add, LinearEquiv.mul_apply]
        _ = (q2Sig hcenter ξ ^ (j + k)) w := by rw [add_comm]
        _ = (q2Sig hcenter ξ ^ j) ((q2Sig hcenter ξ ^ k) w) := by
              rw [pow_add, LinearEquiv.mul_apply]
        _ = (q2Sig hcenter ξ ^ j) w := by rw [hfix]
        _ = w' := hj
  have hσ_dvd : ∀ (k : ℕ) (w : W), w ≠ 0 → (q2Sig hcenter ξ ^ k) w = w →
      orderOf (q2Sig hcenter ξ) ∣ k := by
    intro k w hw hfix
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hσ_fixed_one k w hw hfix
  -- ## `τ`-equivariance of the squaring form, iterated
  have hτquad : ∀ (k : ℕ) (u : V),
      b ((q2Tau hcenter ξ ^ k) u) ((q2Tau hcenter ξ ^ k) u) =
        (q2Sig hcenter ξ ^ k) (b u u) := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
        intro u
        have h1 : (q2Tau hcenter ξ ^ (k + 1)) u = q2Tau hcenter ξ ((q2Tau hcenter ξ ^ k) u) := by
          rw [pow_succ', LinearEquiv.mul_apply]
        have h2 : (q2Sig hcenter ξ ^ (k + 1)) (b u u) =
            q2Sig hcenter ξ ((q2Sig hcenter ξ ^ k) (b u u)) := by
          rw [pow_succ', LinearEquiv.mul_apply]
        rw [h1, h2, q2Tau_quad hcenter ξ ((q2Tau hcenter ξ ^ k) u), ih u]
  have hτ_dvd : ∀ (k : ℕ) (u : V), u ≠ 0 → (q2Tau hcenter ξ ^ k) u = u →
      orderOf (q2Sig hcenter ξ) ∣ k := by
    intro k u hu hfix
    have hbu : b u u ≠ 0 := fun h0 => hu ((b_self_eq_zero_iff hinvol hcenter u).mp h0)
    apply hσ_dvd k (b u u) hbu
    rw [← hτquad k u, hfix]
  have hτfree_aux : ∀ k : ℕ, 0 < k → k < Nat.card V - 1 → ∀ u : V, u ≠ 0 →
      (q2Tau hcenter ξ ^ k) u ≠ u := by
    intro k hk0 hklt u hu hfix
    have h1 : orderOf (q2Sig hcenter ξ) ∣ k := hτ_dvd k u hu hfix
    rw [hσord, ← hcardV] at h1
    have h2 : k = 0 := Nat.eq_zero_of_dvd_of_lt h1 hklt
    omega
  -- ## the Singer structure on `V` and on `W`
  have hτtrans : ∀ a d : V, a ≠ 0 → d ≠ 0 → ∃ k : ℕ, (q2Tau hcenter ξ ^ k) a = d :=
    q2_transitive_of_free_linear (q2Tau hcenter ξ) hτfree_aux
  have hτord : orderOf (q2Tau hcenter ξ) = Nat.card V - 1 :=
    q2_orderOf_of_transitive_linear (q2Tau hcenter ξ) (by rw [hcardV]; omega) hτtrans
  have hτfree : ∀ v : V, q2Tau hcenter ξ v = v → v = 0 := by
    intro v hv
    by_contra hv0
    have h1 : orderOf (q2Sig hcenter ξ) ∣ 1 := hτ_dvd 1 v hv0 (by simpa using hv)
    rw [hσord] at h1
    have h2 : Nat.card W - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hσfree : ∀ w : W, q2Sig hcenter ξ w = w → w = 0 := by
    intro w hw
    by_contra hw0
    have h1 : q2Sig hcenter ξ ^ 1 = 1 := hσ_fixed_one 1 w hw0 (by simpa using hw)
    have h2 : orderOf (q2Sig hcenter ξ) = 1 := by
      have h3 : q2Sig hcenter ξ = 1 := by simpa using h1
      rw [h3, orderOf_one]
    rw [hσord] at h2
    omega
  have hτord' : orderOf (q2Tau hcenter ξ) = 2 ^ n - 1 := by rw [hτord, hVn]
  have hσord' : orderOf (q2Sig hcenter ξ) = 2 ^ n - 1 := by rw [hσord, hnW]
  obtain ⟨φ, ν, hν, hφ⟩ :=
    exists_singer_iso hnpos hVn (q2Tau hcenter ξ) hτord' hτfree
  obtain ⟨ψ, lam, hlam, hψ⟩ :=
    exists_singer_iso hnpos hnW (q2Sig hcenter ξ) hσord' hσfree
  -- ## the squaring form in Singer coordinates
  let Q' : GaloisField 2 n → GaloisField 2 n := fun α => ψ (b (φ.symm α) (φ.symm α))
  have hQ'0 : Q' 0 = 0 := by
    show ψ (b (φ.symm 0) (φ.symm 0)) = 0
    rw [map_zero, Biadd.zero_left (b := b) (0 : V), map_zero]
  have hQ'ne : ∀ α : GaloisField 2 n, α ≠ 0 → Q' α ≠ 0 := by
    intro α hα
    show ψ (b (φ.symm α) (φ.symm α)) ≠ 0
    intro h0
    have h1 : b (φ.symm α) (φ.symm α) = 0 := by
      have := congrArg (fun x => ψ.symm x) h0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have h2 : φ.symm α = 0 := (b_self_eq_zero_iff hinvol hcenter _).mp h1
    exact hα (by rw [← LinearEquiv.apply_symm_apply φ α, h2, map_zero])
  let B' : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun x y => ψ (b (φ.symm x) (φ.symm y) + b (φ.symm y) (φ.symm x))
  have hBadd1 : ∀ u u' d : V,
      b (u + u') d + b d (u + u') = (b u d + b d u) + (b u' d + b d u') := by
    intro u u' d
    rw [Biadd.add_left (b := b) u u' d, Biadd.add_right (b := b) d u u']
    abel
  have hBadd2 : ∀ u d d' : V,
      b u (d + d') + b (d + d') u = (b u d + b d u) + (b u d' + b d' u) := by
    intro u d d'
    rw [Biadd.add_right (b := b) u d d', Biadd.add_left (b := b) d d' u]
    abel
  have hQ'polar : ∀ x y : GaloisField 2 n, Q' (x + y) + Q' x + Q' y = B' x y := by
    intro x y
    show ψ (b (φ.symm (x + y)) (φ.symm (x + y))) + ψ (b (φ.symm x) (φ.symm x)) +
        ψ (b (φ.symm y) (φ.symm y)) =
      ψ (b (φ.symm x) (φ.symm y) + b (φ.symm y) (φ.symm x))
    have hm : φ.symm (x + y) = φ.symm x + φ.symm y := map_add φ.symm x y
    rw [← map_add ψ (b (φ.symm (x + y)) (φ.symm (x + y))) (b (φ.symm x) (φ.symm x)),
      ← map_add ψ (b (φ.symm (x + y)) (φ.symm (x + y)) + b (φ.symm x) (φ.symm x))
        (b (φ.symm y) (φ.symm y))]
    rw [hm, q2_b_polar (b := b) (φ.symm x) (φ.symm y)]
  have hB'1 : ∀ a c d : GaloisField 2 n, B' (a + c) d = B' a d + B' c d := by
    intro a c d
    show ψ (b (φ.symm (a + c)) (φ.symm d) + b (φ.symm d) (φ.symm (a + c))) =
      ψ (b (φ.symm a) (φ.symm d) + b (φ.symm d) (φ.symm a)) +
        ψ (b (φ.symm c) (φ.symm d) + b (φ.symm d) (φ.symm c))
    have hm : φ.symm (a + c) = φ.symm a + φ.symm c := map_add φ.symm a c
    rw [hm, hBadd1 (φ.symm a) (φ.symm c) (φ.symm d),
      ← map_add ψ (b (φ.symm a) (φ.symm d) + b (φ.symm d) (φ.symm a))
        (b (φ.symm c) (φ.symm d) + b (φ.symm d) (φ.symm c))]
  have hB'2 : ∀ a c d : GaloisField 2 n, B' a (c + d) = B' a c + B' a d := by
    intro a c d
    show ψ (b (φ.symm a) (φ.symm (c + d)) + b (φ.symm (c + d)) (φ.symm a)) =
      ψ (b (φ.symm a) (φ.symm c) + b (φ.symm c) (φ.symm a)) +
        ψ (b (φ.symm a) (φ.symm d) + b (φ.symm d) (φ.symm a))
    have hm : φ.symm (c + d) = φ.symm c + φ.symm d := map_add φ.symm c d
    rw [hm, hBadd2 (φ.symm a) (φ.symm c) (φ.symm d),
      ← map_add ψ (b (φ.symm a) (φ.symm c) + b (φ.symm c) (φ.symm a))
        (b (φ.symm a) (φ.symm d) + b (φ.symm d) (φ.symm a))]
  have hQ'add1 : ∀ α α' γ : GaloisField 2 n,
      Q' (α + α' + γ) + Q' (α + α') + Q' γ =
        (Q' (α + γ) + Q' α + Q' γ) + (Q' (α' + γ) + Q' α' + Q' γ) := by
    intro α α' γ
    rw [hQ'polar (α + α') γ, hQ'polar α γ, hQ'polar α' γ]
    exact hB'1 α α' γ
  have hQ'add2 : ∀ α γ γ' : GaloisField 2 n,
      Q' (α + (γ + γ')) + Q' α + Q' (γ + γ') =
        (Q' (α + γ) + Q' α + Q' γ) + (Q' (α + γ') + Q' α + Q' γ') := by
    intro α γ γ'
    rw [hQ'polar α (γ + γ'), hQ'polar α γ, hQ'polar α γ']
    exact hB'2 α γ γ'
  have hQ'ξ : ∀ α : GaloisField 2 n, Q' ((ν : GaloisField 2 n) * α) =
      (lam : GaloisField 2 n) * Q' α := by
    intro α
    have h1 : φ.symm ((ν : GaloisField 2 n) * α) =
        q2Tau hcenter ξ (φ.symm α) := by
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    show ψ (b (φ.symm ((ν : GaloisField 2 n) * α)) (φ.symm ((ν : GaloisField 2 n) * α))) =
      (lam : GaloisField 2 n) * ψ (b (φ.symm α) (φ.symm α))
    rw [h1]
    rw [show b (q2Tau hcenter ξ (φ.symm α)) (q2Tau hcenter ξ (φ.symm α)) =
      q2Sig hcenter ξ (b (φ.symm α) (φ.symm α)) from q2Tau_quad hcenter ξ (φ.symm α)]
    rw [hψ]
  -- ## `B'` is `ξ`-equivariant, so the two Singer cycles are not Frobenius conjugate
  have hpolar_tau : ∀ u v : V, b (q2Tau hcenter ξ u) (q2Tau hcenter ξ v) +
      b (q2Tau hcenter ξ v) (q2Tau hcenter ξ u) = q2Sig hcenter ξ (b u v + b v u) := by
    intro u v
    rw [← q2_b_polar (b := b) (q2Tau hcenter ξ u) (q2Tau hcenter ξ v)]
    rw [show q2Tau hcenter ξ u + q2Tau hcenter ξ v = q2Tau hcenter ξ (u + v) from
      (map_add (q2Tau hcenter ξ) u v).symm]
    rw [q2Tau_quad hcenter ξ (u + v), q2Tau_quad hcenter ξ u, q2Tau_quad hcenter ξ v]
    rw [← map_add (f := q2Sig hcenter ξ), ← map_add (f := q2Sig hcenter ξ)]
    rw [q2_b_polar (b := b) u v]
  have hB'alt : ∀ a : GaloisField 2 n, B' a a = 0 := by
    intro a
    show ψ (b (φ.symm a) (φ.symm a) + b (φ.symm a) (φ.symm a)) = 0
    rw [AddExpTwo.add_self, map_zero]
  have hB'eq : ∀ a d : GaloisField 2 n,
      B' ((ν : GaloisField 2 n) * a) ((ν : GaloisField 2 n) * d) =
        (lam : GaloisField 2 n) * B' a d := by
    intro a d
    have h1 : φ.symm ((ν : GaloisField 2 n) * a) = q2Tau hcenter ξ (φ.symm a) := by
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    have h2 : φ.symm ((ν : GaloisField 2 n) * d) = q2Tau hcenter ξ (φ.symm d) := by
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    show ψ (b (φ.symm ((ν : GaloisField 2 n) * a)) (φ.symm ((ν : GaloisField 2 n) * d)) +
        b (φ.symm ((ν : GaloisField 2 n) * d)) (φ.symm ((ν : GaloisField 2 n) * a))) =
      (lam : GaloisField 2 n) * ψ (b (φ.symm a) (φ.symm d) + b (φ.symm d) (φ.symm a))
    rw [h1, h2, hpolar_tau (φ.symm a) (φ.symm d), hψ]
  have hB'ne : ∃ a d : GaloisField 2 n, B' a d ≠ 0 := by
    obtain ⟨u, hu⟩ : ∃ u : V, u ≠ 0 := by
      haveI : Nontrivial V := by
        haveI : Fintype V := Fintype.ofFinite V
        rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hVn]
        exact Nat.one_lt_pow (by omega) (by norm_num)
      exact exists_ne (0 : V)
    obtain ⟨v, hv⟩ : ∃ v : V, b u v + b v u ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (polar_nondegenerate hcenter u h)
    refine ⟨φ u, φ v, ?_⟩
    show ψ (b (φ.symm (φ u)) (φ.symm (φ v)) + b (φ.symm (φ v)) (φ.symm (φ u))) ≠ 0
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    intro h0
    exact hv (ψ.injective (by rw [h0, map_zero]))
  -- ## the monomial normal form and the Frobenius power `θ`
  have hnotconj : ∀ s : ℕ, (ν : GaloisField 2 n) ≠ (lam : GaloisField 2 n) ^ 2 ^ s :=
    q2_field_not_conj n hnpos ν lam hν hlam B' hB'1 hB'2 hB'alt hB'eq hB'ne
  obtain ⟨φ2, θ, hθne, hθodd, hQ'θ⟩ := q2_monomial_normal_form hnpos ν lam hν hlam hnotconj Q'
    hQ'0 hQ'ne hQ'add1 hQ'add2 hQ'ξ
  -- ## the final coordinates
  let φa : V ≃+ GaloisField 2 n := φ.toAddEquiv
  let ψa : W ≃+ GaloisField 2 n := ψ.toAddEquiv
  let φf : V ≃+ GaloisField 2 n := (φ.trans φ2).toAddEquiv
  have hφf_apply : ∀ u : V, φf u = φ2 (φ u) := fun u => rfl
  have hdiag : ∀ u : V, ψa (b u u) = φf u * θ (φf u) := by
    intro u
    have h := hQ'θ (φ u)
    have h1 : Q' (φ u) = ψ (b u u) := by
      show ψ (b (φ.symm (φ u)) (φ.symm (φ u))) = ψ (b u u)
      rw [LinearEquiv.symm_apply_apply]
    have hψa : ψa (b u u) = ψ (b u u) := rfl
    rw [h1] at h
    rw [← hφf_apply u, ← hψa] at h
    exact h
  -- ## the coboundary
  let δ : V → V → W := fun u v => b u v + ψa.symm (φf u * θ (φf v))
  have hδ1 : ∀ a c d : V, δ (a + c) d = δ a d + δ c d := by
    intro a c d
    show b (a + c) d + ψa.symm (φf (a + c) * θ (φf d)) =
      (b a d + ψa.symm (φf a * θ (φf d))) + (b c d + ψa.symm (φf c * θ (φf d)))
    have h1 : φf (a + c) = φf a + φf c := map_add φf a c
    have h2 : (φf a + φf c) * θ (φf d) = φf a * θ (φf d) + φf c * θ (φf d) :=
      add_mul _ _ _
    have h3 : ψa.symm (φf a * θ (φf d) + φf c * θ (φf d)) =
        ψa.symm (φf a * θ (φf d)) + ψa.symm (φf c * θ (φf d)) := map_add _ _ _
    rw [h1, h2, h3, Biadd.add_left (b := b)]
    abel
  have hδ2 : ∀ a c d : V, δ a (c + d) = δ a c + δ a d := by
    intro a c d
    show b a (c + d) + ψa.symm (φf a * θ (φf (c + d))) =
      (b a c + ψa.symm (φf a * θ (φf c))) + (b a d + ψa.symm (φf a * θ (φf d)))
    have h1 : φf (c + d) = φf c + φf d := map_add φf c d
    have h2 : θ (φf c + φf d) = θ (φf c) + θ (φf d) := map_add θ _ _
    have h3 : φf a * (θ (φf c) + θ (φf d)) = φf a * θ (φf c) + φf a * θ (φf d) :=
      mul_add _ _ _
    have h4 : ψa.symm (φf a * θ (φf c) + φf a * θ (φf d)) =
        ψa.symm (φf a * θ (φf c)) + ψa.symm (φf a * θ (φf d)) := map_add _ _ _
    rw [h1, h2, h3, h4, Biadd.add_right (b := b)]
    abel
  have hδalt : ∀ a : V, δ a a = 0 := by
    intro a
    have h1 : ψa.symm (φf a * θ (φf a)) = b a a := by
      have h := hdiag a
      rw [← h]
      exact AddEquiv.symm_apply_apply ψa _
    show b a a + ψa.symm (φf a * θ (φf a)) = 0
    rw [h1, AddExpTwo.add_self]
  obtain ⟨f, hf⟩ := exists_additive_coboundary δ hδ1 hδ2 hδalt
  let c : GaloisField 2 n → GaloisField 2 n := fun α => ψa (f (φf.symm α))
  refine ⟨n, φf, ψa, θ, c, hnW, hθne, hθodd, ?_⟩
  intro u v
  have hcu : c (φf u) = ψa (f u) := by
    show ψa (f (φf.symm (φf u))) = ψa (f u)
    rw [AddEquiv.symm_apply_apply]
  have hcv : c (φf v) = ψa (f v) := by
    show ψa (f (φf.symm (φf v))) = ψa (f v)
    rw [AddEquiv.symm_apply_apply]
  have hcuv : c (φf u + φf v) = ψa (f (u + v)) := by
    show ψa (f (φf.symm (φf u + φf v))) = ψa (f (u + v))
    have h : φf.symm (φf u + φf v) = u + v := by
      rw [← map_add, AddEquiv.symm_apply_apply]
    rw [h]
  have key : ψa (b u v) + φf u * θ (φf v) = ψa (f (u + v)) + (ψa (f u) + ψa (f v)) := by
    have h1 : δ u v = b u v + ψa.symm (φf u * θ (φf v)) := rfl
    have h2 := hf u v
    rw [h1] at h2
    -- ψa of both sides
    have h3 : ψa (f (u + v) + (f u + f v)) =
        ψa (b u v + ψa.symm (φf u * θ (φf v))) := by rw [h2]
    rw [map_add, map_add, map_add, AddEquiv.apply_symm_apply] at h3
    rw [h3]
  rw [hcu, hcv, hcuv]
  show ψa (b u v) = φf u * θ (φf v) + (ψa (f u) + ψa (f v) + ψa (f (u + v)))
  have := q2_eq_add_of_add_eq key
  rw [this]
  abel

end Work.Higman
