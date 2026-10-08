import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE2A.bswHyps2_of_config2
import Submission.Work.CORE3.exists_orderOf_four_sq_eq
import Submission.Work.CORE3.exists_orderOf_four_in_S0
import Submission.Work.CORE3.exists_mem_centralizer_normalizer_notMem_centralizer
import Submission.Work.CORE3.conj_mul_sq_mem_centralizer
import Submission.Work.CORE3.isMulCommutative_sup_of_conjSub

/-!
# `CORE3` / `Case1aAbelian`: Bender 1981, §3, p. 222 — the third step

Setting (Bender 1981, §3, subcase `Ĥ = H`): `G` is a minimal counterexample, `S ∈ Syl₂(G)` is
dihedral, `t ∈ S₀` is the central involution, `H = C_G(t) = Ĥ` is maximal, `D : Case1aData B`
provides `t₁, t₂ ∈ S − S₀` and an odd prime `p` with `P := O_p(O(H))` centralized by `t₁` and
inverted by `t₂`.  The paper then argues: "For `g ∈ N_G(V₁) − N_H(V₁)`, `P ∩ P^g` is normal in
both `H` and `H^g`, hence is trivial.  It follows that `P P^g`, a normal subgroup of `C_G(V₁)`,
is abelian."

This file records what is *provable* about that step and what the obstruction is.

## Established here

* `conjSub_inf`, `conjSub_conjSub`, `conjSub_conjSub_self`, `conjSub_one` — the calculus of
  `conjSub g K = g K g⁻¹`;
* `conjSub_inf_eq_self_of_conjSub_sq_eq_self` — **the `2`-part of the case analysis**: if `g²`
  normalizes `P`, then `g` normalizes `P ⊓ P^g`.  With the `Case 1` control (`N_G(Y) ≤ H` for
  every `1 ≠ Y ≤ F(U)`, available for `Y = P ⊓ P^g ≤ P ≤ F(U)`) this forces `g ∈ H`, so
  `P ⊓ P^g = ⊥` whenever the image of `g` in `N_G(V₁)/C_G(V₁)` has order `≤ 2`;
* `isMulCommutative_of_inverts` — `P` is abelian, because `t₂` inverts it (`D.inv`);
* `conjSub_inv_le_of_le_normalizer_conjSub`, `conjSub_eq_self_of_le_normalizer_conjSub` —
  **the obstruction**: `N_G(P) = H` and `H ≤ N_G(P^g)` force `H^g = H`, i.e. `g ∈ N_G(H) = H`.
  So the paper's one-line "`P ⊓ P^g` is normal in `H` and in `H^g`" cannot be justified by
  proving `H ≤ N_G(P^g)`; indeed with `N_H(V₁) = C_G(V₁)` one gets `N_G(P ⊓ P^g) = C_G(V₁) ⊆ H`,
  so no normalizer-outside-`H` argument applies.  (Counterexample, found by a reviewer and
  verified in GAP: `G = (C₂²×C₇³)⋊C₃`, `P = ⟨xz,yz⟩`, `F = P`, `H = C_G(V₁)` of index 3 — this
  satisfies every hypothesis *except* simplicity of `G` and has `P ⊓ P^g ≅ C₇ ≠ ⊥`.)

## Remaining gap

The case where `g` acts on `V₁ = ⟨t,t₁⟩` as a `3`-cycle and `N_H(V₁) = C_G(V₁)`: this needs
strictly more of §3 than `Case 1`'s clause (the module `Case1aSetup` and the sibling leaves).
The main theorem below is therefore not yet complete.
-/

namespace Work.CORE3

open Work.GW2

open scoped Pointwise

/-! ## `conjSub`: the calculus of conjugation -/

section ConjSub

variable {G : Type*} [Group G]

theorem conjSub_inf (g : G) (A B : Subgroup G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨Subgroup.mem_map.mpr ⟨y, hy.1, rfl⟩, Subgroup.mem_map.mpr ⟨y, hy.2, rfl⟩⟩
  · rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.mp hx1
    obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.mp hx2
    have hab : (MulAut.conj g) a = (MulAut.conj g) b := by
      change (MulAut.conj g).toMonoidHom a = (MulAut.conj g).toMonoidHom b
      rw [ha', hb']
    have hab' : a = b := (MulAut.conj g).injective hab
    subst hab'
    exact Subgroup.mem_map.mpr ⟨a, ⟨ha, hb⟩, ha'⟩

theorem conjSub_conjSub (h g : G) (K : Subgroup G) :
    conjSub h (conjSub g K) = conjSub (h * g) K := by
  have hcomp : (MulAut.conj h).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj (h * g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [conjSub, conjSub, conjSub, Subgroup.map_map, hcomp]

theorem conjSub_one (K : Subgroup G) : conjSub (1 : G) K = K := by
  have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x; simp
  rw [conjSub, h1, Subgroup.map_id]

theorem conjSub_conjSub_self (g : G) (K : Subgroup G) :
    conjSub g (conjSub g K) = conjSub (g ^ 2) K := by
  rw [conjSub_conjSub, pow_two]

theorem conjSub_inf_eq_self_of_conjSub_sq_eq_self {P : Subgroup G} {g : G}
    (h : conjSub (g ^ 2) P = P) :
    conjSub g (P ⊓ conjSub g P) = P ⊓ conjSub g P := by
  rw [conjSub_inf, conjSub_conjSub_self, h, inf_comm]

theorem isMulCommutative_of_inverts {P : Subgroup G} {s : G}
    (h : ∀ x ∈ P, s * x * s⁻¹ = x⁻¹) : IsMulCommutative P := by
  refine IsMulCommutative.of_comm fun x y => ?_
  have hx : s * (x : G) * s⁻¹ = (x : G)⁻¹ := h x x.2
  have hy : s * (y : G) * s⁻¹ = (y : G)⁻¹ := h y y.2
  have hxy : s * ((x : G) * y) * s⁻¹ = ((x : G) * y)⁻¹ := h (x * y) (P.mul_mem x.2 y.2)
  have key : ((x : G) * y)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ := by
    calc ((x : G) * y)⁻¹ = s * ((x : G) * y) * s⁻¹ := hxy.symm
      _ = (s * (x : G) * s⁻¹) * (s * (y : G) * s⁻¹) := by group
      _ = (x : G)⁻¹ * (y : G)⁻¹ := by rw [hx, hy]
  have key2 : (y : G) * (x : G) = (x : G) * (y : G) := by
    have h1 : ((y : G) * (x : G))⁻¹ = ((x : G) * (y : G))⁻¹ := by
      rw [mul_inv_rev, key]
    exact inv_injective h1
  exact Subtype.ext key2.symm

theorem mem_normalizer_iff_conjSub_eq (x : G) (K : Subgroup G) :
    x ∈ Subgroup.normalizer (K : Set G) ↔ conjSub x K = K :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem conjSub_normalizer (a : G) (K : Subgroup G) :
    conjSub a (Subgroup.normalizer (K : Set G)) = Subgroup.normalizer (conjSub a K : Set G) := by
  have h1 : ∀ y : G, conjSub y K = K →
      conjSub ((MulAut.conj a) y) (conjSub a K) = conjSub a K := by
    intro y hy
    calc conjSub ((MulAut.conj a) y) (conjSub a K)
        = conjSub (((MulAut.conj a) y) * a) K := conjSub_conjSub _ a K
      _ = conjSub (a * y) K := by
          congr 1
          rw [MulAut.conj_apply]; group
      _ = conjSub a (conjSub y K) := (conjSub_conjSub a y K).symm
      _ = conjSub a K := by rw [hy]
  have h2 : ∀ x : G, conjSub x (conjSub a K) = conjSub a K →
      conjSub ((MulAut.conj a⁻¹) x) K = K := by
    intro x hx
    calc conjSub ((MulAut.conj a⁻¹) x) K
        = conjSub (a⁻¹ * (x * a)) K := by
          congr 1
          rw [MulAut.conj_apply]; group
      _ = conjSub a⁻¹ (conjSub (x * a) K) := (conjSub_conjSub a⁻¹ (x * a) K).symm
      _ = conjSub a⁻¹ (conjSub x (conjSub a K)) := by rw [← conjSub_conjSub x a K]
      _ = conjSub a⁻¹ (conjSub a K) := by rw [hx]
      _ = conjSub (a⁻¹ * a) K := conjSub_conjSub a⁻¹ a K
      _ = K := by rw [inv_mul_cancel, conjSub_one]
  ext x
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff_conjSub_eq _ _).mpr
      (h1 y ((mem_normalizer_iff_conjSub_eq _ _).mp hy))
  · intro hx
    refine ⟨(MulAut.conj a⁻¹) x, ?_, ?_⟩
    · exact (mem_normalizer_iff_conjSub_eq _ _).mpr
        (h2 x ((mem_normalizer_iff_conjSub_eq _ _).mp hx))
    · show (MulAut.conj a) ((MulAut.conj a⁻¹) x) = x
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group

/-- **The correct form of Bender's normality step.**  Under the `Case 1` control, the normalizer
of a non-trivial `K = P ⊓ P^g ≤ F` lies in `H ⊓ H^g`. -/
theorem normalizer_inf_conjSub_le {P H F : Subgroup G} {g : G}
    (hPF : P ≤ F)
    (hF1 : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ F → Subgroup.normalizer (Y : Set G) ≤ H)
    (hne : P ⊓ conjSub g P ≠ ⊥) :
    Subgroup.normalizer ((P ⊓ conjSub g P : Subgroup G) : Set G) ≤ H ⊓ conjSub g H := by
  have hNK_le_H : Subgroup.normalizer ((P ⊓ conjSub g P : Subgroup G) : Set G) ≤ H :=
    hF1 _ hne (le_trans inf_le_left hPF)
  -- the conjugate `K' = K^{g⁻¹} = P^{g⁻¹} ⊓ P`
  have hK' : conjSub g⁻¹ (P ⊓ conjSub g P) = conjSub g⁻¹ P ⊓ P := by
    rw [conjSub_inf, conjSub_conjSub, inv_mul_cancel, conjSub_one]
  have hK'_le_F : conjSub g⁻¹ P ⊓ P ≤ F := le_trans inf_le_right hPF
  have hK'_ne : conjSub g⁻¹ P ⊓ P ≠ ⊥ := by
    intro hbot
    have h1 : conjSub g (conjSub g⁻¹ P ⊓ P) = ⊥ := by
      rw [hbot, conjSub, Subgroup.map_bot]
    rw [← hK'] at h1
    have h2 : conjSub g (conjSub g⁻¹ (P ⊓ conjSub g P)) = P ⊓ conjSub g P := by
      rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]
    rw [h2] at h1
    exact hne h1
  have hNK'_le_H :
      Subgroup.normalizer ((conjSub g⁻¹ P ⊓ P : Subgroup G) : Set G) ≤ H :=
    hF1 _ hK'_ne hK'_le_F
  intro x hx
  refine ⟨hNK_le_H hx, ?_⟩
  have hx' : (MulAut.conj g⁻¹) x ∈
      Subgroup.normalizer ((conjSub g⁻¹ P ⊓ P : Subgroup G) : Set G) := by
    rw [← hK', ← conjSub_normalizer g⁻¹ (P ⊓ conjSub g P)]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  refine Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) x, hNK'_le_H hx', ?_⟩
  show (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

end ConjSub

/-! ## The obstruction: the paper's normality claim needs `H ≤ N_G(P^g)`, which forces `g ∈ H` -/

section Obstruction

variable {G : Type*} [Group G]

variable [Finite G]

/-- If `N_G(P) = H` and `H` normalizes `P^g`, then `g⁻¹ H g ≤ H`. -/
theorem conjSub_inv_le_of_le_normalizer_conjSub {P H : Subgroup G} {g : G}
    (hH : Subgroup.normalizer (P : Set G) = H)
    (h : H ≤ Subgroup.normalizer (conjSub g P : Set G)) :
    ∀ y ∈ H, g⁻¹ * y * g ∈ H := by
  intro y hy
  have hy' : conjSub y (conjSub g P) = conjSub g P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h hy)
  rw [← hH, Subgroup.mem_normalizer_iff_map_conj_eq]
  have hkey : conjSub (g⁻¹ * (y * g)) P = P := by
    calc conjSub (g⁻¹ * (y * g)) P
        = conjSub g⁻¹ (conjSub (y * g) P) := (conjSub_conjSub g⁻¹ (y * g) P).symm
      _ = conjSub g⁻¹ (conjSub y (conjSub g P)) := by rw [← conjSub_conjSub y g P]
      _ = conjSub g⁻¹ (conjSub g P) := by rw [hy']
      _ = conjSub ((g⁻¹) * g) P := conjSub_conjSub g⁻¹ g P
      _ = P := by rw [inv_mul_cancel, conjSub_one]
  simpa [conjSub, mul_assoc] using hkey

/-- If `N_G(P) = H` and `H ≤ N_G(P^g)`, then `H` is `g`-invariant. -/
theorem conjSub_eq_self_of_le_normalizer_conjSub {P H : Subgroup G} {g : G}
    (hH : Subgroup.normalizer (P : Set G) = H)
    (h : H ≤ Subgroup.normalizer (conjSub g P : Set G)) :
    conjSub g H = H := by
  have hle := conjSub_inv_le_of_le_normalizer_conjSub hH h
  have hsub_le : conjSub g⁻¹ H ≤ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using hle y hy
  have hsub_eq : conjSub g⁻¹ H = H :=
    Subgroup.eq_of_le_of_card_ge hsub_le (by
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
  calc conjSub g H = conjSub g (conjSub g⁻¹ H) := by rw [hsub_eq]
    _ = conjSub (g * g⁻¹) H := conjSub_conjSub g g⁻¹ H
    _ = H := by rw [mul_inv_cancel, conjSub_one]

namespace Work.CORE3

open Work.GW2

/-! ## The decomposition `C_G(V₁) = (U ⊓ C_G(t₁)) ⊔ V₁`

The sibling `Case1aFrattini` leaf proves `Work.CORE3.Case1aFrattiniApi.CentralizerV1Prop`, i.e.
`C_G(⟨t,t₁⟩) = (U ⊓ C_G(t₁)) ⊔ ⟨t,t₁⟩`.  We re-export it here together with the facts that make
it usable: the two factors are disjoint (so the sum is direct), and everything of interest lies
in the odd factor. -/

section CentralizerV1

variable {G : Type} [Group G] [Finite G]

/-- `V₁ = ⟨t,t₁⟩ ≤ S`. -/
theorem V1_le_S (B : BenderSetup G) (D : Case1aData B) : V1 B D ≤ (B.S : Subgroup G) :=
  sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem)) (Subgroup.zpowers_le.mpr D.t1_mem)

/-- **The decomposition of the centralizer of `V₁`** (Bender 1981 §3, p. 222):
`C_G(V₁) = (U ⊓ C_G(t₁)) ⊔ V₁`.  Proven in the sibling leaf `Case1aFrattini`. -/
theorem centralizer_V1_eq (hBc : BenderCtx G) (T : LocalToolkit) (B : BenderSetup G)
    (D : Case1aData B) :
    Subgroup.centralizer ((V1 B D : Subgroup G) : Set G)
      = (B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) ⊔ V1 B D :=
  Work.CORE3.Work.CORE3.centralizer_V1 (G := G) hBc T B D

/-- The two factors of the decomposition are disjoint, so `C_G(V₁)` is the *direct* product
`(U ⊓ C_G(t₁)) × V₁`. -/
theorem V1_inf_centralizer_t1_eq_bot (B : BenderSetup G) (D : Case1aData B) :
    V1 B D ⊓ (B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) = ⊥ := by
  refine le_bot_iff.mp ?_
  calc V1 B D ⊓ (B.U ⊓ Subgroup.centralizer ({D.t1} : Set G))
      ≤ V1 B D ⊓ B.U := inf_le_inf_left _ inf_le_left
    _ ≤ (B.S : Subgroup G) ⊓ B.U := inf_le_inf_right _ (V1_le_S B D)
    _ = ⊥ := by rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B

end CentralizerV1

/-! ## The enumeration of `V₁ = ⟨t, t₁⟩`

Everything below is the proof of `Case1aAbelian`.  The two ingredients specific to the `3`-cycle
case are delegated: `Work.CORE3.exists_orderOf_four_in_S0` (an order-`4` element of `S₀` squaring
to `t`) and `Work.CORE3.conj_mul_sq_mem_centralizer` (the `S₃`-parity computation). -/

section Enumeration

variable {G : Type} [Group G] [Finite G]

/-- `V₁ = ⟨t, t₁⟩ = {1, t, t₁, t·t₁}`. -/
theorem V1_set (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1aData B) :
    ((V1 B D : Subgroup G) : Set G) = ({1, B.t, D.t1, B.t * D.t1} : Set G) := by
  classical
  have hcomm : B.t * D.t1 = D.t1 * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)
  have hnormalizer : Subgroup.zpowers D.t1 ≤
      Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := by
    have hcen : Subgroup.zpowers D.t1 ≤
        Subgroup.centralizer (Subgroup.zpowers B.t : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hcomm : Commute B.t D.t1) k).eq
    exact le_trans hcen (Subgroup.centralizer_le_normalizer _)
  have hcoe : ((V1 B D : Subgroup G) : Set G)
      = (Subgroup.zpowers B.t : Set G) * (Subgroup.zpowers D.t1 : Set G) := by
    rw [V1]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormalizer
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [hcoe, Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    have ha' : a = 1 ∨ a = B.t :=
      Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two B.t_order ha
    have hb' : b = 1 ∨ b = D.t1 :=
      Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two D.t1_order hb
    rw [← hab]
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · simp
    · simp
    · simp
    · simp [hcomm]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (V1 B D).one_mem
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
    · exact (V1 B D).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))

end Enumeration

/-- Bender 1981 §3, p. 222, third step.  Deliverable `Work.GW2.Case1aAbelianProp`.

For `g ∈ N_G(V₁) − N_H(V₁)` (`V₁ = ⟨t,t₁⟩`, `g ∈ normalizer (⟨t,t₁⟩)`, `g ∉ H`): `P ∩ P^g = ⊥`
and `P P^g` is abelian.

**Proof.**  Suppose `K := P ⊓ P^g ≠ ⊥`.  By `normalizer_inf_conjSub_le`, `N_G(K) ≤ H ⊓ H^g`, so
every element normalizing `K` lies in `H`.

* If `g² ∈ H` then `g² ∈ H ≤ N_G(P)`, so `K` is `g`-invariant and `g ∈ N_G(K) ≤ H` — absurd.
* If `g² ∉ H`: the image of `g` in `Aut(V₁)` has order `3` (it is non-trivial, and its square is
  non-trivial as `g² ∉ H`), so `g` acts on `V₁#` as a `3`-cycle.  The element `s` of order `4`
  in `S₀` with `s² = t` (`exists_orderOf_four_in_S0`) lies in `C_G(t)`, normalizes `V₁` and is
  outside `C_G(V₁)`; hence by `exists_mem_centralizer_normalizer_notMem_centralizer` there is
  `x ∈ N_G(V₁) ∩ C_G(t) − C_G(V₁)`, i.e. `x` acts on `V₁#` as the transposition fixing `t`.
  Since `x ∈ H ≤ N_G(P)` we have `P^{gx} = P^{g}` (`conjSub` is contravariant), and by the
  parity computation `conj_mul_sq_mem_centralizer` the element `(g x)²` lies in `C_G(V₁) ⊆ H`.
  Step `A` applied to `g x ∉ H` gives `P ⊓ P^{gx} = ⊥`, i.e. `K = ⊥` — absurd.

Hence `K = ⊥`, and since `P` and `P^g` are both normal in `C_G(V₁)` with `P ⊓ P^g = ⊥`, the join
`P ⊔ P^g` is abelian (`isMulCommutative_sup_of_conjSub`). -/
theorem Case1aAbelian (I : Case1Inputs) : Case1aAbelianProp := by
  intro G _ _ hFT hBc B hCase1 hHhat D g hgV hgH
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  haveI : IsSimpleGroup G := hBc.simple
  -- Notation: `P = O_p(O(H))`, `V₁ = ⟨t,t₁⟩`.
  set P : Subgroup G := pCoreIn D.p B.U with hPdef
  set V : Subgroup G := Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t1 with hVdef
  -- `P ≤ H` and `P` is abelian (`t₂` inverts it).
  have hP_le_H : P ≤ B.H := (c1aPcoreIn_le_self D.p B.U).trans (Work.CORE2A.bSetup_U_le_H B)
  have hPa : IsMulCommutative P := isMulCommutative_of_inverts (s := D.t2) fun x hx => D.inv x hx
  -- `P ⊴ H` (`O_p(U)` is characteristic in `U = O(H) ⊴ H`).
  have hH_norm_P : B.H ≤ Subgroup.normalizer (P : Set G) := by
    have hHU : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
      simpa [BenderSetup.U, oddCoreIn] using
        (c1aLe_normalizer_map_subtype (K := B.H) (N := oddCore ↥B.H)
          (Work.GW2.oddCore_normal ↥B.H))
    exact hHU.trans (c1aLe_normalizer_pCoreIn D.p B.U)
  have hP_le_F : P ≤ fittingIn B.U := c1aPcoreIn_le_fittingIn D.p B.U
  -- The `Case 1` normalizer control.
  have hF1 : ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ fittingIn B.U →
      Subgroup.normalizer (Y : Set G) ≤ B.H := by
    intro Y hY hYF
    have h := hCase1.2 Y hY hYF
    rwa [hHhat] at h
  -- `V` is a four-group and `V ≤ H`.
  have hV4 : IsFourGroup V := Work.CORE3.Work.CORE3.fourGroup_V1 (G := G) hBc B D
  have htV : B.t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
  have ht1V : D.t1 ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
  have ht_ne : B.t ≠ 1 := by
    intro h
    have hone : orderOf B.t = 1 := by rw [h]; exact orderOf_one
    rw [B.t_order] at hone
    exact absurd hone (by norm_num)
  have ht1_ne : D.t1 ≠ 1 := by
    intro h
    have hone : orderOf D.t1 = 1 := by rw [h]; exact orderOf_one
    rw [D.t1_order] at hone
    exact absurd hone (by norm_num)
  have ht1_ne_t : D.t1 ≠ B.t := fun h => D.t1_nmem (h ▸ B.t_mem)
  have ht_sq : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    rwa [pow_two] at h
  have hV_le_H : V ≤ B.H := by
    rw [hVdef]
    exact sup_le (Subgroup.zpowers_le.mpr (Work.CORE2A.bSetup_S_le_H B (B.S0_le B.t_mem)))
      (Subgroup.zpowers_le.mpr (Work.CORE2A.bSetup_S_le_H B D.t1_mem))
  have hCV_le_H : Subgroup.centralizer (V : Set G) ≤ B.H :=
    Subgroup.centralizer_le (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact htV)
  have commute_of_conj : ∀ {c y : G}, c * y * c⁻¹ = y → y * c = c * y := by
    intro c y h
    calc y * c = (c * y * c⁻¹) * c := by rw [h]
      _ = c * y := by group
  -- **Step A**: `K_y := P ⊓ P^y` is trivial whenever `y ∉ H` but `y² ∈ H`.
  have stepA : ∀ y : G, y ∉ B.H → y ^ 2 ∈ B.H → P ⊓ conjSub y P = ⊥ := by
    intro y hyH hy2
    by_contra hne
    have hNK := normalizer_inf_conjSub_le (P := P) (H := B.H) (F := fittingIn B.U) (g := y)
      hP_le_F hF1 hne
    have hsq : conjSub (y ^ 2) P = P := (mem_normalizer_iff_conjSub_eq _ _).mp (hH_norm_P hy2)
    have hfix : conjSub y (P ⊓ conjSub y P) = P ⊓ conjSub y P :=
      conjSub_inf_eq_self_of_conjSub_sq_eq_self hsq
    have hyN : y ∈ Subgroup.normalizer ((P ⊓ conjSub y P : Subgroup G) : Set G) :=
      (mem_normalizer_iff_conjSub_eq _ _).mpr hfix
    exact hyH (hNK hyN).1
  have hmain : P ⊓ conjSub g P = ⊥ := by
    by_contra hne
    by_cases hg2 : g ^ 2 ∈ B.H
    · exact absurd (stepA g hgH hg2) hne
    · -- `g` acts on `V#` as a `3`-cycle.  Produce `x ∈ N_G(V) ∩ C_G(t) − C_G(V)`.
      obtain ⟨s, hsS0, hsord, hssq⟩ := Work.CORE3.exists_orderOf_four_in_S0 hFT hBc B D
      have hS0comm : ∀ a ∈ B.S0, ∀ b ∈ B.S0, a * b = b * a := by
        intro a ha b hb
        haveI : IsCyclic ↥B.S0 := B.S0_cyclic
        have hcommS : IsMulCommutative ↥B.S0 := IsCyclic.isMulCommutative
        have := hcommS.is_comm.comm (⟨a, ha⟩ : ↥B.S0) (⟨b, hb⟩ : ↥B.S0)
        simpa using this
      have hinvS0 : Inverts D.t1 B.S0 := Work.CORE3.Work.CORE3.t1_inverts_S0 hBc B D
      have ht1_sq : D.t1 * D.t1 = 1 := Work.CORE3.Work.CORE3.t1_sq B D
      have ht1_inv : D.t1⁻¹ = D.t1 := by
        calc D.t1⁻¹ = D.t1⁻¹ * 1 := (mul_one _).symm
          _ = D.t1⁻¹ * (D.t1 * D.t1) := by rw [ht1_sq]
          _ = (D.t1⁻¹ * D.t1) * D.t1 := by group
          _ = 1 * D.t1 := by rw [inv_mul_cancel]
          _ = D.t1 := one_mul _
      have hinv : D.t1 * s * D.t1 = s⁻¹ := by
        have h := hinvS0 s hsS0
        rwa [ht1_inv] at h
      obtain ⟨x, hxC, hxN, hxnotC⟩ :=
        Work.CORE3.exists_mem_centralizer_normalizer_notMem_centralizer
          (G := G) hsS0 B.t_mem hS0comm hsord hssq ht1_sq hinv ht_ne
      have hVsetLoc : (V : Set G) = ({1, B.t, D.t1, B.t * D.t1} : Set G) := V1_set hBc B D
      -- `x` commutes with `t` and swaps `t₁` with `t·t₁`.
      have hxt : x * B.t * x⁻¹ = B.t := by
        have h := (Subgroup.mem_centralizer_iff.mp hxC) B.t (Set.mem_singleton B.t)
        rw [← h]; group
      have hmem : x * D.t1 * x⁻¹ ∈ V := ((Subgroup.mem_normalizer_iff.mp hxN) D.t1).mp ht1V
      have hxt1 : x * D.t1 * x⁻¹ = B.t * D.t1 := by
        have hmem' : x * D.t1 * x⁻¹ ∈ (V : Set G) := hmem
        rw [hVsetLoc] at hmem'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
        rcases hmem' with h | h | h | h
        · -- impossible: `x * t₁ * x⁻¹ ≠ 1`
          exfalso
          apply ht1_ne
          have := congrArg (fun z => x⁻¹ * z * x) h
          simpa [mul_assoc] using this
        · -- impossible: `x * t₁ * x⁻¹ ≠ t`
          exfalso
          have h2 : B.t * D.t1 = 1 := by
            have h3 : x * (B.t * D.t1) * x⁻¹ = 1 := by
              calc x * (B.t * D.t1) * x⁻¹
                  = (x * B.t * x⁻¹) * (x * D.t1 * x⁻¹) := by group
                _ = B.t * B.t := by rw [hxt, h]
                _ = 1 := ht_sq
            have := congrArg (fun z => x⁻¹ * z * x) h3
            simpa [mul_assoc] using this
          apply ht1_ne_t
          calc D.t1 = 1 * D.t1 := by rw [one_mul]
            _ = (B.t * B.t) * D.t1 := by rw [ht_sq]
            _ = B.t * (B.t * D.t1) := by group
            _ = B.t * 1 := by rw [h2]
            _ = B.t := by rw [mul_one]
        · -- impossible: then `x` centralises `V`
          exfalso
          apply hxnotC
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : y = 1 ∨ y = B.t ∨ y = D.t1 ∨ y = B.t * D.t1 := by
            have := hy
            rw [hVsetLoc] at this
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
          have hx_t1 : D.t1 * x = x * D.t1 := commute_of_conj h
          have hx_t : B.t * x = x * B.t := commute_of_conj hxt
          rcases hy' with rfl | rfl | rfl | rfl
          · simp
          · exact commute_of_conj hxt
          · exact hx_t1
          · calc (B.t * D.t1) * x = B.t * (D.t1 * x) := by group
              _ = B.t * (x * D.t1) := by rw [hx_t1]
              _ = (B.t * x) * D.t1 := by group
              _ = (x * B.t) * D.t1 := by rw [hx_t]
              _ = x * (B.t * D.t1) := by group
        · exact h
      -- `g` moves `t` and moves `t ^ g`, so `g` acts as a 3-cycle
      have h1g : g * B.t * g⁻¹ ≠ B.t := by
        intro h
        apply hgH
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact commute_of_conj h
      have h2g : g * (g * B.t * g⁻¹) * g⁻¹ ≠ B.t := by
        intro h
        apply hg2
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have h' : (g * g) * B.t * (g * g)⁻¹ = B.t := by
          have := h
          rwa [show g * (g * B.t * g⁻¹) * g⁻¹ = (g * g) * B.t * (g * g)⁻¹ from by group] at this
        simpa [pow_two] using commute_of_conj h'
      -- the parity computation
      have hxg_sq : (x * g) * (x * g) ∈ Subgroup.centralizer (V : Set G) :=
        Work.CORE3.conj_mul_sq_mem_centralizer hV4 htV ht1V ht_ne ht1_ne_t hxN hxt hxt1 hgV
          h1g h2g
      have hgx_sq : (g * x) * (g * x) ∈ Subgroup.centralizer (V : Set G) := by
        have hconjC := Work.CORE3.Work.CORE3.cj_map_conj_le_centralizer V
          (Subgroup.centralizer (V : Set G)) g hgV le_rfl
        have hmemC : g * ((x * g) * (x * g)) * g⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          hconjC (Subgroup.mem_map.mpr ⟨(x * g) * (x * g), hxg_sq,
            by show (MulAut.conj g) ((x * g) * (x * g)) = g * ((x * g) * (x * g)) * g⁻¹
               rw [MulAut.conj_apply]⟩)
        have heq : g * ((x * g) * (x * g)) * g⁻¹ = (g * x) * (g * x) := by group
        rw [heq] at hmemC
        exact hmemC
      -- `P ^ (g * x) = P ^ g`
      have hxN_P : x ∈ Subgroup.normalizer (P : Set G) := hH_norm_P hxC
      have hPconj : conjSub (g * x) P = conjSub g P := by
        rw [← conjSub_conjSub g x P, (mem_normalizer_iff_conjSub_eq x P).mp hxN_P]
      -- Step A with `y = g * x`
      have hgx_notH : g * x ∉ B.H := by
        intro h
        apply hgH
        have hg_eq : g = (g * x) * x⁻¹ := by group
        rw [hg_eq]
        exact B.H.mul_mem h (B.H.inv_mem hxC)
      have hgx2H : (g * x) ^ 2 ∈ B.H := by
        rw [pow_two]
        exact hCV_le_H hgx_sq
      have := stepA (g * x) hgx_notH hgx2H
      rw [hPconj] at this
      exact absurd this hne
  refine ⟨hmain, ?_⟩
  -- `P` and `P^g` are both normal in `C_G(V)`, with `P ⊓ P^g = ⊥`; hence the join is abelian.
  have hP_le_C : P ≤ Subgroup.centralizer (V : Set G) := by
    rw [hVdef, Subgroup.centralizer_sup, Work.CORE3.Work.CORE3.centralizer_zpowers_eq,
      Work.CORE3.Work.CORE3.centralizer_zpowers_eq]
    exact le_inf hP_le_H D.cent
  have hPg_le_C : conjSub g P ≤ Subgroup.centralizer (V : Set G) :=
    Work.CORE3.Work.CORE3.cj_map_conj_le_centralizer V P g hgV hP_le_C
  have hC_le_NP : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    hCV_le_H.trans hH_norm_P
  have hC_le_NPg : Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (conjSub g P : Set G) := by
    have h1 : Subgroup.centralizer (V : Set G) ≤ conjSub g B.H := by
      intro c hc
      rw [conjSub, Work.CORE3.Work.CORE3.cj_mem_map_conj_iff]
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have htg : g * B.t * g⁻¹ ∈ V := ((Subgroup.mem_normalizer_iff.mp hgV) B.t).mp htV
      have hcc : (g * B.t * g⁻¹) * c = c * (g * B.t * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hc) _ htg
      calc B.t * (g⁻¹ * c * g) = g⁻¹ * ((g * B.t * g⁻¹) * c) * g := by group
        _ = g⁻¹ * (c * (g * B.t * g⁻¹)) * g := by rw [hcc]
        _ = (g⁻¹ * c * g) * B.t := by group
    have h2 : conjSub g B.H ≤ conjSub g (Subgroup.normalizer (P : Set G)) :=
      Subgroup.map_mono hH_norm_P
    rw [conjSub_normalizer] at h2
    exact h1.trans h2
  exact isMulCommutative_sup_of_conjSub hPa (hPg_le_C.trans hC_le_NP)
    (hP_le_C.trans hC_le_NPg) hmain

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aAbelian` (the name the CORE3 assembly uses) and as
`Work.CORE3.Work.CORE3.Case1aAbelian` (the skeleton's namespace layout). -/
theorem Case1aAbelian (I : Case1Inputs) : Case1aAbelianProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aAbelian I
