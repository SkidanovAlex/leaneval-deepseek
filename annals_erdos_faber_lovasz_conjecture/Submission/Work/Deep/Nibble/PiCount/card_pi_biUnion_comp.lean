import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Work.Deep.Nibble.PiCount

/-- Membership in a union indexed by all of `ι`. -/
private lemma mem_biUnion_univ {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (B : ι → Finset α) {x : α} : x ∈ Finset.univ.biUnion B ↔ ∃ e, x ∈ B e := by
  simp [Finset.mem_biUnion]

/-- A canonical choice of the block containing a point of the union of the blocks. -/
private noncomputable def blockOf {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (B : ι → Finset α) (x : α) (hx : x ∈ Finset.univ.biUnion B) : ι :=
  ((mem_biUnion_univ B).mp hx).choose

/-- The chosen block really contains the point. -/
private lemma mem_blockOf {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (B : ι → Finset α) (x : α) (hx : x ∈ Finset.univ.biUnion B) :
    x ∈ B (blockOf B x hx) := ((mem_biUnion_univ B).mp hx).choose_spec

/-- Disjointness makes the chosen block the only block containing the point. -/
private lemma blockOf_eq {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (B : ι → Finset α) (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k)) {x : α}
    (hx : x ∈ Finset.univ.biUnion B) {e : ι} (he : x ∈ B e) : blockOf B x hx = e := by
  by_contra h
  exact (Finset.disjoint_left.mp (hdisj (blockOf B x hx) e h) (mem_blockOf B x hx)) he

/-- Evaluating a family of block colourings at a point is independent of which
(equal) index of the block one uses. -/
private lemma block_apply_transport {α : Type*} {ι : Type*} {p : ℕ} (B : ι → Finset α)
    {e e' : ι} (h : e = e') {x : α} (hx : x ∈ B e) (hx' : x ∈ B e')
    (f : ∀ e, ↑(B e) → Fin p) : f e ⟨x, hx⟩ = f e' ⟨x, hx'⟩ := by
  subst h
  exact congrArg (f _) (Subtype.ext rfl)

/-- A colouring of the whole type is determined by its restrictions to the pairwise
disjoint blocks and by its restriction to the complement of their union. -/
private noncomputable def compEquiv {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Finset α)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (P : ∀ e : ι, (↑(B e) → Fin p) → Prop) [∀ e, DecidablePred (P e)] :
    {c : α → Fin p // ∀ e, P e (fun x : ↑(B e) => c x)} ≃
      ((∀ e, {f : ↑(B e) → Fin p // P e f}) ×
        ({x : α // x ∉ Finset.univ.biUnion B} → Fin p)) where
  toFun c := (fun e => ⟨fun x => c.1 ↑x, c.2 e⟩, fun x => c.1 ↑x)
  invFun y :=
    ⟨fun x => if hx : x ∈ Finset.univ.biUnion B then
        (y.1 (blockOf B x hx)).1 ⟨x, mem_blockOf B x hx⟩
      else y.2 ⟨x, hx⟩,
     fun e => by
      have key : (fun x : ↑(B e) =>
          (if hx : (x : α) ∈ Finset.univ.biUnion B then
            (y.1 (blockOf B (x : α) hx)).1 ⟨(x : α), mem_blockOf B (x : α) hx⟩
          else y.2 ⟨(x : α), hx⟩)) = (y.1 e).1 := by
        funext x
        have hx : ((x : α)) ∈ Finset.univ.biUnion B := (mem_biUnion_univ B).mpr ⟨e, x.2⟩
        rw [dif_pos hx]
        have hb : blockOf B (↑x) hx = e := blockOf_eq B hdisj hx x.2
        rw [block_apply_transport B hb (mem_blockOf B (↑x) hx) x.2 (fun e' => (y.1 e').1)]
      rw [key]
      exact (y.1 e).2⟩
  left_inv c := by
    apply Subtype.ext
    funext x
    dsimp only
    by_cases hx : x ∈ Finset.univ.biUnion B
    · rw [dif_pos hx]
    · rw [dif_neg hx]
  right_inv y := by
    apply Prod.ext
    · funext e
      apply Subtype.ext
      funext x
      dsimp only
      have hx : ((x : α)) ∈ Finset.univ.biUnion B := (mem_biUnion_univ B).mpr ⟨e, x.2⟩
      rw [dif_pos hx]
      have hb : blockOf B (↑x) hx = e := blockOf_eq B hdisj hx x.2
      rw [block_apply_transport B hb (mem_blockOf B (↑x) hx) x.2 (fun e' => (y.1 e').1)]
    · funext x
      dsimp only
      rw [dif_neg x.2]

/-- Colourings of a finite type, with arbitrary conditions imposed on pairwise disjoint "blocks".  The colourings of the blocks and of the complement of their union are independent, so the number of colourings satisfying all the block conditions is `p ^ (number of free coordinates)` times the product of the local counts. -/
theorem card_pi_biUnion_comp {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Finset α)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (P : ∀ e : ι, (↑(B e) → Fin p) → Prop) [∀ e, DecidablePred (P e)] :
    ((Finset.univ.filter (fun c : α → Fin p =>
        ∀ e, P e (fun x : ↑(B e) => c x))).card : ℝ)
      = (p : ℝ) ^ (Fintype.card α - (Finset.univ.biUnion B).card)
        * ∏ e, ((Finset.univ.filter (P e)).card : ℝ) := by
  have hcard : (Finset.univ.filter (fun c : α → Fin p =>
        ∀ e, P e (fun x : ↑(B e) => c x))).card
      = (∏ e, (Finset.univ.filter (P e)).card)
        * p ^ (Fintype.card α - (Finset.univ.biUnion B).card) := by
    rw [← Fintype.card_subtype (fun c : α → Fin p => ∀ e, P e (fun x : ↑(B e) => c x))]
    rw [Fintype.card_congr (compEquiv B hdisj P), Fintype.card_prod, Fintype.card_pi]
    congr 1
    · apply Finset.prod_congr rfl
      intro e _
      rw [Fintype.card_subtype]
    · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard]
  push_cast
  ring

end Work.Deep.Nibble.PiCount
