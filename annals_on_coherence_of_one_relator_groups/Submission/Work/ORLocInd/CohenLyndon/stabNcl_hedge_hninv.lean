/-
# The normal closure of `of r` acts freely on the edges of the Bass--Serre tree,
and without inversions

Let `K` be a group, `A B ≤ K`, `φ : A ≃* B`, `r ∈ K`, and suppose that the normal closure
`M = ⟪r⟫_K` of `r` meets both `A` and `B` trivially.  Writing `E = HNNExtension K A B φ` and
`N = ⟪of r⟫_E`, we show that the action of `N` on the Bass--Serre tree `V = E ⧸ ofE(K)` of the
HNN extension has trivial edge stabilizers and is without inversions:

* `stab_Ncl_eq_bot` : the `N`-stabilizer of every arrow of the tree is trivial;
* `hninv_Ncl_aux` : no element of `N` reverses an arrow.

These are the hypotheses `hedge` and `hninv` under which the normal closure `N` of a "hypoelliptic"
element splits as a free product of its vertex stabilizers (see
`Work.ORBassSerre.Action.freeProduct_of_vertexStabilizers`).

## The edge stabilizers

Every arrow joins `⟦g⟧` to `⟦g * of m * t^ε⟧`.  An element of `N` fixing such an arrow lies in
`g⁻¹ N g`, and conjugating by `g⁻¹` we are reduced to the arrow `⟦1⟧ – ⟦t^ε⟧`.  The key
ingredients are

* `hnn_inf_range_eq` : `N ⊓ ofE(K) = ofE(M)`;
* `tconjMemRange` : `t^u * of k * t^{-u} ∈ ofE(K) ↔ k ∈ toSubgroup A B u`;

from which the membership `k'` of `N` that `N`-stabilizes an arrow is forced into
`M ⊓ toSubgroup A B (-ε) = ⊥`.

## The absence of inversions

There is a homomorphism `ρ : E →* ℤˣ` killing `K` and sending the stable letter `t` to `-1`;
it satisfies `ρ x = (-1)^(tlen x)`.  Since `ρ` is trivial on `N`, the `t`-length — i.e. the
`N`-function on the tree — is preserved modulo `2` by `N`.  As adjacent vertices have
`t`-length differing by `1`, and inverting an arrow would move a vertex to its neighbour without
changing the parity, `N` acts without inversions.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.hnnSetup

set_option autoImplicit false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

/-! ## The absence of inversions

A homomorphism `E →* ℤˣ` detecting the parity of the `t`-length. -/

section Parity

variable {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B} {r : K}

/-- The homomorphism `HNNExtension K A B φ →* ℤˣ` which is trivial on `K` and sends the stable
letter `t` to `-1`.  Its value on `x` is `(-1) ^ tlen x`. -/
noncomputable def tpar : HNNExtension K A B φ →* ℤˣ :=
  HNNExtension.lift (1 : K →* ℤˣ) (-1) (by intro a; simp)

theorem tpar_of (k : K) : tpar (A := A) (B := B) (φ := φ) (HNNExtension.of k) = 1 := by
  simp [tpar]

theorem tpar_t : tpar (A := A) (B := B) (φ := φ) (HNNExtension.t : HNNExtension K A B φ) = -1 := by
  simp [tpar]

open HNNExtension in
theorem tpar_prod (w : Work.ORBassSerre.HNN.RedWord (A := A) (B := B)) :
    tpar (A := A) (B := B) (φ := φ) (NormalWord.ReducedWord.prod φ w)
      = (-1 : ℤˣ) ^ w.toList.length := by
  rw [NormalWord.ReducedWord.prod, map_mul, MonoidHom.map_list_prod]
  rw [tpar_of (w.head), one_mul, List.map_map]
  have h : (List.map (⇑tpar ∘ fun x : ℤˣ × K =>
      (HNNExtension.t : HNNExtension K A B φ) ^ ((x.1 : ℤˣ) : ℤ) * HNNExtension.of x.2) w.toList)
     = List.map (fun _ => (-1 : ℤˣ)) w.toList := by
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [map_mul, map_zpow, tpar_of, mul_one, tpar_t]
    rcases Int.units_eq_one_or x.1 with h1 | h1
    · rw [h1]; norm_num
    · rw [h1]; norm_num
  rw [h, List.map_const', List.prod_replicate]

theorem tpar_eq (g : HNNExtension K A B φ) :
    tpar (A := A) (B := B) (φ := φ) g = (-1 : ℤˣ) ^ Work.ORBassSerre.HNN.tlen g := by
  obtain ⟨w, hw⟩ := Work.ORBassSerre.HNN.exists_reducedWord (A := A) (B := B) (φ := φ) g
  rw [← hw, tpar_prod, Work.ORBassSerre.HNN.tlen_prod]

theorem tpar_mem_Ncl {n : HNNExtension K A B φ}
    (hn : n ∈ Ncl (A := A) (B := B) (φ := φ) (r := r)) :
    tpar (A := A) (B := B) (φ := φ) n = 1 := by
  have h : Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ≤
      MonoidHom.ker (tpar (A := A) (B := B) (φ := φ)) := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact MonoidHom.mem_ker.mpr (tpar_of r)
  exact MonoidHom.mem_ker.mp (h hn)

/-- An element of `Ncl` preserves the parity of the `t`-length. -/
theorem even_tlen_mul_Ncl {n : HNNExtension K A B φ}
    (hn : n ∈ Ncl (A := A) (B := B) (φ := φ) (r := r)) (g : HNNExtension K A B φ) :
    Even (Work.ORBassSerre.HNN.tlen (n * g)) ↔ Even (Work.ORBassSerre.HNN.tlen g) := by
  have h1 : (-1 : ℤˣ) ^ Work.ORBassSerre.HNN.tlen (n * g)
      = (-1 : ℤˣ) ^ Work.ORBassSerre.HNN.tlen g := by
    rw [← tpar_eq (A := A) (B := B) (φ := φ) (n * g), ← tpar_eq g, map_mul,
      tpar_mem_Ncl hn, one_mul]
  rw [← neg_one_pow_eq_one_iff_even (show (-1 : ℤˣ) ≠ 1 by decide),
      ← neg_one_pow_eq_one_iff_even (show (-1 : ℤˣ) ≠ 1 by decide), h1]

/-- Adjacent vertices of the Bass--Serre tree have `t`-lengths of opposite parity. -/
theorem even_N_adj {X Y : Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)}
    (h : Work.ORBassSerre.HNN.adj X Y) :
    Even (Work.ORBassSerre.HNN.N X) ↔ ¬ Even (Work.ORBassSerre.HNN.N Y) := by
  rcases Work.ORBassSerre.HNN.N_adj h with h2 | h2
  · rw [h2]; simp only [Nat.even_add_one, not_not]
  · rw [h2]; simp only [Nat.even_add_one]

/-- **The normal closure of `of r` acts without inversions** on the Bass--Serre tree of the
HNN extension. -/
theorem hninv_Ncl_aux :
    Work.ORBassSerre.ActsWithoutInversions ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))
      (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)) := by
  intro n e heq
  have hleft : n • e.left = e.right := by
    calc n • e.left = (n • e).left := (Work.ORBassSerre.GraphAction.smul_left n e).symm
      _ = e.reverse.left := congrArg Quiver.Total.left heq
      _ = e.right := rfl
  obtain ⟨g, hg⟩ := Quotient.exists_rep e.left
  have hpar : Even (Work.ORBassSerre.HNN.N (n • e.left)) ↔
      Even (Work.ORBassSerre.HNN.N e.left) := by
    rw [← hg]
    change Even (Work.ORBassSerre.HNN.N
        ((n : HNNExtension K A B φ) • Work.ORBassSerre.HNN.qmk g)) ↔
      Even (Work.ORBassSerre.HNN.N (Work.ORBassSerre.HNN.qmk g))
    rw [Work.ORBassSerre.HNN.smul_qmk, Work.ORBassSerre.HNN.N_qmk, Work.ORBassSerre.HNN.N_qmk]
    exact even_tlen_mul_Ncl n.2 g
  have heven := hpar
  rw [congrArg Work.ORBassSerre.HNN.N hleft] at heven
  have hc := even_N_adj (A := A) (B := B) (φ := φ) e.hom.down.2
  rw [← heven] at hc
  exact (fun h => (hc.mp h) h) (hc.mpr (fun h => (hc.mp h) h))

end Parity

/-! ## Triviality of the edge stabilizers -/

section Stabilizer

variable {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B} {r : K}

/-- The image of `S` in the HNN extension meets `Ncl` in the image of `Mcl ⊓ S`. -/
theorem Ncl_inf_map_ofE (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) (S : Subgroup K) :
    Ncl (A := A) (B := B) (φ := φ) (r := r) ⊓
        S.map (HNNExtension.of (A := A) (B := B) (φ := φ))
      = (Mcl (r := r) ⊓ S).map (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
  have hI := hnn_inf_range_eq (A := A) (B := B) (φ := φ) (r := r) hA hB
  apply le_antisymm
  · rintro x ⟨hxN, hxS⟩
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp hxS
    obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp (show x ∈ (Mcl (r := r)).map
      (HNNExtension.of (A := A) (B := B) (φ := φ)) from by
        rw [← hI]; exact ⟨hxN, ⟨s, hse⟩⟩)
    have hms : m = s := HNNExtension.of_injective (A := A) (B := B) φ (hme.trans hse.symm)
    exact Subgroup.mem_map.mpr ⟨m, Subgroup.mem_inf.mpr ⟨hm, by rw [hms]; exact hs⟩, hme⟩
  · rw [le_inf_iff]
    constructor
    · calc (Mcl (r := r) ⊓ S).map (HNNExtension.of (A := A) (B := B) (φ := φ))
          ≤ (Mcl (r := r)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) :=
            Subgroup.map_mono inf_le_left
        _ = Ncl (A := A) (B := B) (φ := φ) (r := r) ⊓
              (HNNExtension.of (A := A) (B := B) (φ := φ)).range := hI.symm
        _ ≤ Ncl (A := A) (B := B) (φ := φ) (r := r) := inf_le_left
    · exact Subgroup.map_mono inf_le_right

/-- Membership in the stabilizer of `⟦h⟧` in the HNN extension, in terms of conjugation. -/
theorem mem_stab_qmk_iff' (h k : HNNExtension K A B φ) :
    k ∈ MulAction.stabilizer (HNNExtension K A B φ) (Work.ORBassSerre.HNN.qmk h) ↔
      h⁻¹ * k * h ∈ (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
  rw [MulAction.mem_stabilizer_iff, Work.ORBassSerre.HNN.smul_qmk,
    Work.ORBassSerre.HNN.qmk_eq_iff]
  have key : (k * h)⁻¹ * h = (h⁻¹ * k * h)⁻¹ := by group
  rw [key, Subgroup.inv_mem_iff]

set_option maxHeartbeats 800000 in
/-- **Every arrow of the Bass--Serre tree has trivial `Ncl`-stabilizer.** -/
theorem stab_Ncl_eq_bot (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥)
    (e : Quiver.Total (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ))) :
    MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) e = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  have hfix : Work.ORBassSerre.GraphAction.smulTotal (n : HNNExtension K A B φ) e = e :=
    MulAction.mem_stabilizer_iff.mp hn
  have hfixL : (n : HNNExtension K A B φ) • e.left = e.left := by
    have h := congrArg Quiver.Total.left hfix
    rwa [Work.ORBassSerre.GraphAction.smul_left] at h
  have hfixR : (n : HNNExtension K A B φ) • e.right = e.right := by
    have h := congrArg Quiver.Total.right hfix
    rwa [Work.ORBassSerre.GraphAction.smul_right] at h
  obtain ⟨g, hg⟩ := Quotient.exists_rep e.left
  have hg' : Work.ORBassSerre.HNN.qmk g = e.left := hg
  have hadj : Work.ORBassSerre.HNN.adj e.left e.right := e.hom.down.2
  rw [← hg'] at hadj
  obtain ⟨m, ε, hmε⟩ := (Work.ORBassSerre.HNN.adj_iff g e.right).mp hadj
  have hL : (n : HNNExtension K A B φ) ∈ MulAction.stabilizer (HNNExtension K A B φ)
      (Work.ORBassSerre.HNN.qmk g) := by
    rw [MulAction.mem_stabilizer_iff, hg']; exact hfixL
  have hR : (n : HNNExtension K A B φ) ∈ MulAction.stabilizer (HNNExtension K A B φ)
      (Work.ORBassSerre.HNN.qmk (Work.ORBassSerre.HNN.step g m ε)) := by
    rw [MulAction.mem_stabilizer_iff, ← hmε]; exact hfixR
  have hmemL : g⁻¹ * (n : HNNExtension K A B φ) * g ∈
      (HNNExtension.of (A := A) (B := B) (φ := φ)).range := (mem_stab_qmk_iff' g n).mp hL
  have hmemR : (Work.ORBassSerre.HNN.step g m ε)⁻¹ * (n : HNNExtension K A B φ) *
      (Work.ORBassSerre.HNN.step g m ε) ∈
      (HNNExtension.of (A := A) (B := B) (φ := φ)).range :=
    (mem_stab_qmk_iff' (Work.ORBassSerre.HNN.step g m ε) n).mp hR
  have hNcl : g⁻¹ * (n : HNNExtension K A B φ) * g ∈ Ncl (A := A) (B := B) (φ := φ) (r := r) := by
    have := (Subgroup.normalClosure_normal (s := ({HNNExtension.of r} :
      Set (HNNExtension K A B φ)))).conj_mem (n : HNNExtension K A B φ) n.2 g⁻¹
    simpa using this
  obtain ⟨k', hk'M, hk'e⟩ := Subgroup.mem_map.mp (show g⁻¹ * (n : HNNExtension K A B φ) * g ∈
      (Mcl (r := r)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) from by
        rw [← hnn_inf_range_eq (A := A) (B := B) (φ := φ) (r := r) hA hB]
        exact ⟨hNcl, hmemL⟩)
  have hstep : (Work.ORBassSerre.HNN.step g m ε)⁻¹ * (n : HNNExtension K A B φ) *
      (Work.ORBassSerre.HNN.step g m ε)
      = Work.ORBassSerre.HNN.tpow (-ε) * HNNExtension.of (m⁻¹ * k' * m) *
        Work.ORBassSerre.HNN.tpow ε := by
    have h1 : (Work.ORBassSerre.HNN.step g m ε)⁻¹ * (n : HNNExtension K A B φ) *
        (Work.ORBassSerre.HNN.step g m ε)
        = Work.ORBassSerre.HNN.tpow (-ε) * ((HNNExtension.of m)⁻¹ *
            (g⁻¹ * (n : HNNExtension K A B φ) * g) * HNNExtension.of m) *
          Work.ORBassSerre.HNN.tpow ε := by
      simp only [Work.ORBassSerre.HNN.step_eq, Work.ORBassSerre.HNN.tpow, Units.val_neg, zpow_neg]
      group
    rw [h1, ← hk'e]
    rw [show HNNExtension.of (m⁻¹ * k' * m) = (HNNExtension.of m)⁻¹ * HNNExtension.of k' *
      HNNExtension.of m from by rw [map_mul, map_mul, map_inv]]
  have hmem2 : Work.ORBassSerre.HNN.tpow (-ε) * HNNExtension.of (m⁻¹ * k' * m) *
      Work.ORBassSerre.HNN.tpow ε ∈ (HNNExtension.of (A := A) (B := B) (φ := φ)).range :=
    hstep ▸ hmemR
  have hkS : m⁻¹ * k' * m ∈ HNNExtension.toSubgroup A B (-ε) := by
    have h3 : Work.ORBassSerre.HNN.tpow (-ε) * HNNExtension.of (m⁻¹ * k' * m) *
        Work.ORBassSerre.HNN.tpow (-(-ε)) ∈
        (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
      rw [neg_neg]; exact hmem2
    exact (Work.ORBassSerre.HNN.tconjMemRange (-ε) (m⁻¹ * k' * m)).mp h3
  have hkM : m⁻¹ * k' * m ∈ Mcl (r := r) := by
    have := (Subgroup.normalClosure_normal (s := ({r} : Set K))).conj_mem k' hk'M m⁻¹
    simpa using this
  have hMclinf : Mcl (r := r) ⊓ HNNExtension.toSubgroup A B (-ε) = ⊥ := by
    rcases Int.units_eq_one_or (-ε) with h1 | h1
    · rw [h1, HNNExtension.toSubgroup_one]; exact hA
    · rw [h1, HNNExtension.toSubgroup_neg_one]; exact hB
  have hk1 : m⁻¹ * k' * m = 1 := by
    have hb : m⁻¹ * k' * m ∈ Mcl (r := r) ⊓ HNNExtension.toSubgroup A B (-ε) := ⟨hkM, hkS⟩
    rw [hMclinf] at hb
    simpa using hb
  have hk'1 : k' = 1 := by
    have h2 : k' = m * (m⁻¹ * k' * m) * m⁻¹ := by group
    rw [hk1] at h2; simpa using h2
  refine Subtype.ext ?_
  have hn1 : g⁻¹ * (n : HNNExtension K A B φ) * g = 1 := by
    rw [← hk'e, hk'1]; simp
  calc (n : HNNExtension K A B φ) = g * (g⁻¹ * (n : HNNExtension K A B φ) * g) * g⁻¹ := by
        group
    _ = g * 1 * g⁻¹ := by rw [hn1]
    _ = 1 := by group

end Stabilizer

open Quiver in
theorem stabNcl_hedge_hninv {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B} {r : K}
    (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) :
    (∀ e : Quiver.Total (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)),
        MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) e = ⊥) ∧
      Work.ORBassSerre.ActsWithoutInversions ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))
        (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)) :=
  ⟨fun e => stab_Ncl_eq_bot hA hB e,
    hninv_Ncl_aux (K := K) (A := A) (B := B) (φ := φ) (r := r)⟩

end Work.ORLocInd.CohenLyndon
