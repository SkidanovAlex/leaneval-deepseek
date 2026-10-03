import Mathlib
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetter_F2_generation
import Submission.Work.OROneRel.gateBookkeeping
import Submission.Work.OROneRel.presentedGroup_union_amalgam
import Submission.Work.OROneRel.unionAmalgam_normalForm
import Submission.Work.OROneRel.telescoping_britton
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.band_halves_inter
import Submission.Work.OROneRel.mem_winRho_range_iff
import Submission.Work.OROneRel.hnnConjMap_injective_of_tree
import Submission.Work.OROneRel.freeGroup_fin_two_hopfian
import Submission.Work.ORBassSerre.HNN.Defs

/-!
# Injectivity of the comparison map of the two-letter band

The target `Work.OROneRel.band_hnnConjMap_injective` is the injectivity of

  `hnnConjMap H τ : HNN(↥H, H ⊓ τ⁻¹Hτ, τ(H ⊓ τ⁻¹Hτ)τ⁻¹, conj_τ) →* F₂`

for `H = (winRho Wt (tlW p q) 0 (p*q)).range = π₁` of the band graph of the `ℤ`-cover of the
two-petal rose and `τ = tlLowTau p q`.

## The proof strategy (see `NOTES_twoLetter_hnnConjMap_routes.md`, §10)

The single geometric input is the **intersection formula** `Work.OROneRel.tlHalves_inter` (`(INT)`)

  `Ple c ⊓ Pge (c+1) = Ak c`

for the two halves `Ple c = ⟨Hk k : k ≤ c⟩`, `Pge c = ⟨Hk k : c ≤ k⟩` of the line of translated
band vertices `Hk k = τᵏHτ⁻ᵏ` and the gates `Ak c = Hk c ⊓ Hk (c+1)`.  With it, the injectivity is
the "descent"/normal-form argument of §10.3, implemented here in the equivalent form of the
*Britton* statement `Work.OROneRel.band_britton` (a chain-reduced word spells a non-trivial element
of `F₂`).

## Contents of this file

* `tlTau` and the membership dictionary `mem_tlHk_iff`: the elementary dictionary between `tlHk k`
  and `tlH`;
* `cohom_eq_one_of_mem_tlH`, `cohom_eq_one_of_mem_tlHk`: the weight facts (`H ≤ ker χ`);
* the partial sums `tlS`, the conjugates `tlK` and the telescoping identity;
* the peak/valley consequences of the chain condition;
* `band_britton` (the normal form) and the assembly of the target from it.
-/

namespace Work.OROneRel

universe u

/-! ## §1 Setup: the deck element and its weight -/

/-- **The deck element** `tlLowTau p q` of the band window `[0, p*q]`. -/
noncomputable abbrev tlTau (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    FreeGroup (Fin 2) :=
  tlLowTau p q hp hq hcop

/-- `cohom (tlW p q) τ = 1`. -/
theorem tlTau_cohom (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    cohom (tlW p q) (tlTau p q hp hq hcop) = Multiplicative.ofAdd 1 :=
  tlLowTau_cohom p q hp hq hcop

/-- The walk of `τ` lies in the band. -/
theorem tlTau_walk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlTau p q hp hq hcop)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) :=
  tlLowTau_walk p q hp hq hcop

/-! ## §2 The weight facts -/

/-- **Every element of the band vertex has weight `1`.**  This is the `⊆` direction read through the
walk dictionary `Work.OROneRel.mem_winRho_range_iff`: an element of the range is spelled by a closed
walk of the window, and a closed walk has vanishing weight. -/
theorem cohom_eq_one_of_mem_tlH (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    {x : FreeGroup (Fin 2)} (hx : x ∈ tlH p q Wt) :
    cohom (tlW p q) x = 1 := by
  obtain ⟨L, _hwalk, hlsig, hmk⟩ :=
    (mem_winRho_range_iff p q hp hq hcop Wt hW0 hcoh hwin htree x).mp hx
  rw [← hmk, cohom_mk, hlsig]
  simp

/-- The weight of every element of the translated band vertex `Hk k = τᵏHτ⁻ᵏ` is `1`. -/
theorem cohom_eq_one_of_mem_tlHk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt i)),
        coverEdge e ∈ winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    {k : ℤ} {x : FreeGroup (Fin 2)} (hx : x ∈ tlHk p q hp hq hcop Wt k) :
    cohom (tlW p q) x = 1 := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hxy : x = (tlTau p q hp hq hcop) ^ k * y * ((tlTau p q hp hq hcop) ^ k)⁻¹ := by
    rw [← hyx]
    show MulAut.conj ((tlTau p q hp hq hcop) ^ k) y = _
    rw [MulAut.conj_apply]
  rw [hxy]
  have hcoht : cohom (tlW p q) (tlTau p q hp hq hcop) = Multiplicative.ofAdd 1 :=
    tlTau_cohom p q hp hq hcop
  have hcohy : cohom (tlW p q) y = 1 :=
    cohom_eq_one_of_mem_tlH p q hp hq hcop hW0 hcoh hwin htree hy
  rw [map_mul, map_mul, map_inv, map_zpow, hcoht, hcohy, mul_one]
  exact mul_inv_cancel _

/-- **The membership dictionary for the translated band vertices**: `x ∈ Hk k` if and only if its
`τ^{-k}`-conjugate lies in the band vertex `H`. -/
theorem mem_tlHk_iff (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (k : ℤ) (x : FreeGroup (Fin 2)) :
    x ∈ tlHk p q hp hq hcop Wt k ↔
      (tlTau p q hp hq hcop) ^ (-k) * x * (tlTau p q hp hq hcop) ^ k ∈ tlH p q Wt := by
  rw [tlHk, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : x = (tlTau p q hp hq hcop) ^ k * y * ((tlTau p q hp hq hcop) ^ k)⁻¹ := by
      rw [← hyx]
      show MulAut.conj ((tlTau p q hp hq hcop) ^ k) y = _
      rw [MulAut.conj_apply]
    rw [hxy]
    have hcancel : (tlTau p q hp hq hcop) ^ (-k) *
        ((tlTau p q hp hq hcop) ^ k * y * ((tlTau p q hp hq hcop) ^ k)⁻¹) *
        (tlTau p q hp hq hcop) ^ k = y := by group
    rw [hcancel]
    exact hy
  · intro hx
    refine ⟨(tlTau p q hp hq hcop) ^ (-k) * x * (tlTau p q hp hq hcop) ^ k, hx, ?_⟩
    show (MulAut.conj ((tlTau p q hp hq hcop) ^ k))
        ((tlTau p q hp hq hcop) ^ (-k) * x * (tlTau p q hp hq hcop) ^ k) = x
    rw [MulAut.conj_apply]
    group

/-! ## §3 The partial sums of the exponents of a list, and the conjugates -/

/-- **The partial sums** of the `ℤ`-exponents of a list `L`: `tlS L i` is the sum of the exponents
of the first `i` letters of `L` (constant once `i ≥ L.length`). -/
noncomputable def tlS (L : List (ℤˣ × FreeGroup (Fin 2))) (i : ℕ) : ℤ :=
  ((L.take i).map (fun x => (x.1 : ℤ))).sum

@[simp] theorem tlS_zero (L : List (ℤˣ × FreeGroup (Fin 2))) : tlS L 0 = 0 := by
  simp [tlS]

/-- `tlS` is constant past the length of the list. -/
theorem tlS_take_le {L : List (ℤˣ × FreeGroup (Fin 2))} {i : ℕ} (h : L.length ≤ i) :
    tlS L i = tlS L L.length := by
  have h1 : L.take i = L.take L.length := by
    rw [List.take_of_length_le h, List.take_length]
  unfold tlS
  rw [h1]

/-- The recursion of the partial sums. -/
theorem tlS_succ (L : List (ℤˣ × FreeGroup (Fin 2))) {i : ℕ} (h : i < L.length) :
    tlS L (i + 1) = tlS L i + ((L[i]).1 : ℤ) := by
  unfold tlS
  rw [← List.take_append_getElem (l := L) h, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The recursion of the partial sums, in `getD`-form. -/
theorem tlS_succ_getD (L : List (ℤˣ × FreeGroup (Fin 2))) {i : ℕ} (h : i < L.length) :
    tlS L (i + 1) = tlS L i + ((L.getD i 1).1 : ℤ) := by
  rw [tlS_succ L h, List.getD_eq_getElem L 1 h]

/-- The partial sums of a cons. -/
theorem tlS_cons (x : ℤˣ × FreeGroup (Fin 2)) (L : List (ℤˣ × FreeGroup (Fin 2))) (i : ℕ) :
    tlS (x :: L) (i + 1) = (x.1 : ℤ) + tlS L i := by
  unfold tlS
  rw [List.take_succ_cons, List.map_cons, List.sum_cons, List.map_take]

/-- **The conjugated letters**: for `1 ≤ i ≤ L.length`, `tlK L i` is the `τ ^ (tlS L i)`-conjugate of
the `i`-th letter of `L`. -/
noncomputable def tlK (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (L : List (ℤˣ × FreeGroup (Fin 2))) (i : ℕ) : FreeGroup (Fin 2) :=
  (tlTau p q hp hq hcop) ^ (tlS L i) * (L.getD (i - 1) 1).2 *
    (tlTau p q hp hq hcop) ^ (-(tlS L i))

/-- **The conjugated letter lies in the translated band vertex of its level.** -/
theorem tlK_mem_tlHk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (L : List (ℤˣ × FreeGroup (Fin 2)))
    (hL : ∀ i : Fin L.length, (L.get i).2 ∈ tlH p q Wt) {i : ℕ}
    (hi : 1 ≤ i) (hi' : i ≤ L.length) :
    tlK p q hp hq hcop L i ∈ tlHk p q hp hq hcop Wt (tlS L i) := by
  have hpos : i - 1 < L.length := by omega
  rw [mem_tlHk_iff, tlK, List.getD_eq_getElem L 1 hpos]
  have hcancel : (tlTau p q hp hq hcop) ^ (-(tlS L i)) *
      ((tlTau p q hp hq hcop) ^ (tlS L i) * (L[i - 1]).2 *
        (tlTau p q hp hq hcop) ^ (-(tlS L i))) * (tlTau p q hp hq hcop) ^ (tlS L i)
      = (L[i - 1]).2 := by group
  rw [hcancel]
  exact hL ⟨i - 1, hpos⟩

/-- **The list of conjugated letters** (with shift `s`): the `i`-th entry is
`τ^(s + S_{i+1}) · g_i · τ^(-(s + S_{i+1}))`, defined by recursion on the list. -/
noncomputable def tlKList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    List (ℤˣ × FreeGroup (Fin 2)) → ℤ → List (FreeGroup (Fin 2))
  | [], _ => []
  | x :: L, s => ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
        (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) ::
      tlKList p q hp hq hcop L (s + (x.1 : ℤ))

@[simp] theorem tlKList_nil (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (s : ℤ) : tlKList p q hp hq hcop [] s = [] := rfl

/-- The recursion of the conjugated list. -/
theorem tlKList_cons (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (x : ℤˣ × FreeGroup (Fin 2)) (L : List (ℤˣ × FreeGroup (Fin 2))) (s : ℤ) :
    tlKList p q hp hq hcop (x :: L) s =
      ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
          (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) ::
        tlKList p q hp hq hcop L (s + (x.1 : ℤ)) := rfl

theorem tlKList_length (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (L : List (ℤˣ × FreeGroup (Fin 2))) (s : ℤ) :
    (tlKList p q hp hq hcop L s).length = L.length := by
  induction L generalizing s with
  | nil => simp
  | cons x L ih => rw [tlKList_cons, List.length_cons, List.length_cons, ih]

/-- **Telescoping, in the recursive form.** -/
theorem tlK_telescope_aux (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ (L : List (ℤˣ × FreeGroup (Fin 2))) (s : ℤ),
      (tlTau p q hp hq hcop) ^ s *
          (L.map (fun x : ℤˣ × FreeGroup (Fin 2) =>
            (tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2)).prod
        = (tlKList p q hp hq hcop L s).prod *
          (tlTau p q hp hq hcop) ^ (s + tlS L L.length) := by
  intro L
  induction L with
  | nil => intro s; simp
  | cons x L ih =>
      intro s
      rw [List.map_cons, List.prod_cons, tlKList_cons, List.prod_cons]
      have hlen : tlS (x :: L) (x :: L).length = (x.1 : ℤ) + tlS L L.length := by
        rw [List.length_cons, tlS_cons]
      rw [hlen]
      have hih := ih (s + (x.1 : ℤ))
      calc (tlTau p q hp hq hcop) ^ s *
            ((tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2 *
              (List.map (fun x : ℤˣ × FreeGroup (Fin 2) =>
                (tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2) L).prod)
          = ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
                (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) *
              ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) *
                (List.map (fun x : ℤˣ × FreeGroup (Fin 2) =>
                  (tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2) L).prod) := by group
        _ = ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
                (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) *
              ((tlKList p q hp hq hcop L (s + (x.1 : ℤ))).prod *
                (tlTau p q hp hq hcop) ^ ((s + (x.1 : ℤ)) + tlS L L.length)) := by
              rw [hih]
        _ = ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
                (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) *
              (tlKList p q hp hq hcop L (s + (x.1 : ℤ))).prod *
              (tlTau p q hp hq hcop) ^ ((s + (x.1 : ℤ)) + tlS L L.length) := by group
        _ = ((tlTau p q hp hq hcop) ^ (s + (x.1 : ℤ)) * x.2 *
                (tlTau p q hp hq hcop) ^ (-(s + (x.1 : ℤ)))) *
              (tlKList p q hp hq hcop L (s + (x.1 : ℤ))).prod *
              (tlTau p q hp hq hcop) ^ (s + ((x.1 : ℤ) + tlS L L.length)) := by
              rw [← add_assoc]

/-- **Telescoping**, with `s = 0` and using the vanishing of the total exponent. -/
theorem tlK_telescope_zero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (L : List (ℤˣ × FreeGroup (Fin 2))) (hn : tlS L L.length = 0) :
    (L.map (fun x : ℤˣ × FreeGroup (Fin 2) =>
        (tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2)).prod
      = (tlKList p q hp hq hcop L 0).prod := by
  have h := tlK_telescope_aux p q hp hq hcop L 0
  simp only [zero_add, zpow_zero, one_mul, mul_one, hn] at h
  exact h


/-- **The lower gate** `A = H ⊓ τ⁻¹Hτ` of the pair `(H, τ)`. -/
noncomputable abbrev tlGateA (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) : Subgroup (FreeGroup (Fin 2)) :=
  hnnEdgeA (tlH p q Wt) (tlTau p q hp hq hcop)

/-- **The upper gate** `B = τAτ⁻¹ = H ⊓ τHτ⁻¹` of the pair `(H, τ)`. -/
noncomputable abbrev tlGateB (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) : Subgroup (FreeGroup (Fin 2)) :=
  hnnEdgeB (tlH p q Wt) (tlTau p q hp hq hcop)

/-- `g ∈ H ⊓ τ⁻¹Hτ` if and only if `g ∈ H` and `τ g τ⁻¹ ∈ H`. -/
theorem mem_gateA_iff (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} {g : FreeGroup (Fin 2)} :
    g ∈ tlGateA p q hp hq hcop Wt ↔
      g ∈ tlH p q Wt ∧ (tlTau p q hp hq hcop) * g * (tlTau p q hp hq hcop)⁻¹ ∈ tlH p q Wt := by
  rw [tlGateA, hnnEdgeA, Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, hmap⟩
    obtain ⟨h, hh, hhe⟩ := Subgroup.mem_map.mp hmap
    refine ⟨hg, ?_⟩
    have h1 : MulAut.conj ((tlTau p q hp hq hcop))⁻¹ h = g := hhe
    rw [MulAut.conj_apply] at h1
    have h2 : (tlTau p q hp hq hcop) * g * (tlTau p q hp hq hcop)⁻¹ = h := by
      rw [← h1]; group
    rw [h2]
    exact hh
  · rintro ⟨hg, hτ⟩
    refine ⟨hg, Subgroup.mem_map.mpr ⟨(tlTau p q hp hq hcop) * g * (tlTau p q hp hq hcop)⁻¹,
      hτ, ?_⟩⟩
    show MulAut.conj ((tlTau p q hp hq hcop))⁻¹
        ((tlTau p q hp hq hcop) * g * (tlTau p q hp hq hcop)⁻¹) = g
    rw [MulAut.conj_apply]
    group

/-- **At a peak of the exponent profile the conjugated letter avoids the gate below.** -/
theorem tlK_notMem_tlAk_of_peak (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (L : List (ℤˣ × FreeGroup (Fin 2)))
    (hL : ∀ i : Fin L.length, (L.get i).2 ∈ tlH p q Wt)
    (hchain : L.IsChain (fun a b => a.2 ∈ HNNExtension.toSubgroup
        (tlGateA p q hp hq hcop Wt) (tlGateB p q hp hq hcop Wt) a.1 → a.1 = b.1))
    {i : ℕ} (hi : 1 ≤ i) (hi2 : i + 1 ≤ L.length)
    (hu1 : (L[i - 1]).1 = 1) (hu2 : (L[i]).1 = -1) :
    tlK p q hp hq hcop L i ∉ tlAk p q hp hq hcop Wt (tlS L i - 1) := by
  intro hmem
  have hpos : i - 1 < L.length := by omega
  have hk : tlK p q hp hq hcop L i ∈ tlHk p q hp hq hcop Wt (tlS L i - 1) :=
    (Subgroup.mem_inf.mp hmem).1
  have hconj := (mem_tlHk_iff p q hp hq hcop Wt (tlS L i - 1) (tlK p q hp hq hcop L i)).mp hk
  have hkform : tlK p q hp hq hcop L i =
      (tlTau p q hp hq hcop) ^ (tlS L i) * (L[i - 1]).2 *
        (tlTau p q hp hq hcop) ^ (-(tlS L i)) := by
    rw [tlK, List.getD_eq_getElem L 1 hpos]
  rw [hkform] at hconj
  have hS : tlS L i = tlS L (i - 1) + 1 := by
    have h := tlS_succ L hpos
    rw [show i - 1 + 1 = i from by omega] at h
    rw [h, hu1]
    norm_num
  have hsimp : (tlTau p q hp hq hcop) ^ (-(tlS L i - 1)) *
      ((tlTau p q hp hq hcop) ^ (tlS L i) * (L[i - 1]).2 *
        (tlTau p q hp hq hcop) ^ (-(tlS L i))) * (tlTau p q hp hq hcop) ^ (tlS L i - 1)
      = (tlTau p q hp hq hcop) * (L[i - 1]).2 * (tlTau p q hp hq hcop)⁻¹ := by
    rw [hS]
    group
  rw [hsimp] at hconj
  have hrel := (List.isChain_iff_getElem.mp hchain) (i - 1) (by omega)
  have hnotA : (L[i - 1]).2 ∉ tlGateA p q hp hq hcop Wt := by
    intro hcon
    have h1 : (L[i - 1]).1 = (L[i]).1 := by
      simpa [Nat.sub_add_cancel hi] using hrel (by rw [hu1]; exact hcon)
    rw [hu1, hu2] at h1
    exact absurd h1 (by decide)
  rw [mem_gateA_iff] at hnotA
  exact hnotA ⟨hL ⟨i - 1, hpos⟩, hconj⟩

/-- **At a valley of the exponent profile the conjugated letter avoids the gate above.** -/
theorem tlK_notMem_tlAk_of_valley (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (L : List (ℤˣ × FreeGroup (Fin 2)))
    (hL : ∀ i : Fin L.length, (L.get i).2 ∈ tlH p q Wt)
    (hchain : L.IsChain (fun a b => a.2 ∈ HNNExtension.toSubgroup
        (tlGateA p q hp hq hcop Wt) (tlGateB p q hp hq hcop Wt) a.1 → a.1 = b.1))
    {i : ℕ} (hi : 1 ≤ i) (hi2 : i + 1 ≤ L.length)
    (hu1 : (L[i - 1]).1 = -1) (hu2 : (L[i]).1 = 1) :
    tlK p q hp hq hcop L i ∉ tlAk p q hp hq hcop Wt (tlS L i) := by
  intro hmem
  have hpos : i - 1 < L.length := by omega
  have hk : tlK p q hp hq hcop L i ∈ tlHk p q hp hq hcop Wt (tlS L i + 1) :=
    (Subgroup.mem_inf.mp hmem).2
  have hconj := (mem_tlHk_iff p q hp hq hcop Wt (tlS L i + 1) (tlK p q hp hq hcop L i)).mp hk
  have hkform : tlK p q hp hq hcop L i =
      (tlTau p q hp hq hcop) ^ (tlS L i) * (L[i - 1]).2 *
        (tlTau p q hp hq hcop) ^ (-(tlS L i)) := by
    rw [tlK, List.getD_eq_getElem L 1 hpos]
  rw [hkform] at hconj
  have hsimp : (tlTau p q hp hq hcop) ^ (-(tlS L i + 1)) *
      ((tlTau p q hp hq hcop) ^ (tlS L i) * (L[i - 1]).2 *
        (tlTau p q hp hq hcop) ^ (-(tlS L i))) * (tlTau p q hp hq hcop) ^ (tlS L i + 1)
      = (tlTau p q hp hq hcop)⁻¹ * (L[i - 1]).2 * (tlTau p q hp hq hcop) := by group
  rw [hsimp] at hconj
  have hrel := (List.isChain_iff_getElem.mp hchain) (i - 1) (by omega)
  have hnotB : (L[i - 1]).2 ∉ tlGateB p q hp hq hcop Wt := by
    intro hcon
    have h1 : (L[i - 1]).1 = (L[i]).1 := by
      simpa [Nat.sub_add_cancel hi] using hrel (by rw [hu1]; exact hcon)
    rw [hu1, hu2] at h1
    exact absurd h1 (by decide)
  have hnotB' : (L[i - 1]).2 ∉
      (tlGateA p q hp hq hcop Wt).map (MulAut.conj (tlTau p q hp hq hcop)) := by
    simpa only [tlGateB, hnnEdgeB] using hnotB
  refine hnotB' (Subgroup.mem_map.mpr ⟨(tlTau p q hp hq hcop)⁻¹ * (L[i - 1]).2 *
    (tlTau p q hp hq hcop), ?_, ?_⟩)
  · rw [mem_gateA_iff]
    refine ⟨hconj, ?_⟩
    rw [show (tlTau p q hp hq hcop) * ((tlTau p q hp hq hcop)⁻¹ * (L[i - 1]).2 *
      (tlTau p q hp hq hcop)) * (tlTau p q hp hq hcop)⁻¹ = (L[i - 1]).2 from by group]
    exact hL ⟨i - 1, hpos⟩
  · show MulAut.conj (tlTau p q hp hq hcop)
        ((tlTau p q hp hq hcop)⁻¹ * (L[i - 1]).2 * (tlTau p q hp hq hcop)) = (L[i - 1]).2
    rw [MulAut.conj_apply]
    group

/-! ## §3.5 Elementary consequences of (INT) and the subgroup bookkeeping

The descent of `NOTES_twoLetter_hnnConjMap_routes.md` §10.3 was refuted in general (see
`Submission/Work/OROneRel/band_cosetGraph_isTree.lean`, §3bis) and its "cap"/"≤-variant" repair is
*also* false (see `Submission/Work/OROneRel/NOTES_band_hnnConjMap_state.md` §3 for the explicit
five-letter counterexample `(1,0,-1,0,1)` in the band `p = 2, q = 3`).  The following facts, on the
other hand, are correct and are used by *any* normal-form argument, so they are recorded here. -/

/-- **A conjugate of the band vertex that misses the gate below is not in the lower half.**  This is
`(INT)` at `c - 1` together with `tlHk c ⊆ tlPge c`: an element of `tlHk c` which also lies in
`tlPle (c-1)` lies in `tlPle (c-1) ⊓ tlPge c = tlAk (c-1)`. -/
theorem tlHk_notMem_tlPle_sub_one_of_notMem_tlAk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2))
    (hINT : ∀ c : ℤ, tlPle p q hp hq hcop Wt c ⊓ tlPge p q hp hq hcop Wt (c + 1)
      = tlAk p q hp hq hcop Wt c)
    {c : ℤ} {u : FreeGroup (Fin 2)} (hu : u ∈ tlHk p q hp hq hcop Wt c)
    (hu2 : u ∉ tlAk p q hp hq hcop Wt (c - 1)) :
    u ∉ tlPle p q hp hq hcop Wt (c - 1) := by
  intro hmem
  refine hu2 ?_
  rw [← hINT (c - 1)]
  refine ⟨hmem, ?_⟩
  rw [show c - 1 + 1 = c from by ring]
  exact tlHk_le_tlPge p q hp hq hcop Wt le_rfl hu

/-- **The lower half is not enlarged by right multiplication by its own elements.** -/
theorem notMem_mul_of_notMem_of_mem {G : Type*} [Group G] {P : Subgroup G} {u d : G}
    (hu : u ∉ P) (hd : d ∈ P) : u * d ∉ P := fun h =>
  hu (by
    have : u = (u * d) * d⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hd))

/-- **The lower half is not enlarged by left multiplication by its own elements.** -/
theorem notMem_mul_of_mem_of_notMem {G : Type*} [Group G] {P : Subgroup G} {d w : G}
    (hd : d ∈ P) (hw : w ∉ P) : d * w ∉ P := fun h =>
  hw (by
    have : w = d⁻¹ * (d * w) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hd) h)

/-! ## §3.6 The climb: enlarging the base of an HNN decomposition

The following observation is the engine of a new route to the target (see the note
`NOTES_band_hnnConjMap_climb.md`).  Let `K ≤ K' ≤ G`, `τ ∈ G`, and suppose that `K'` is generated
by `K` and its `τ`-conjugate:

  `K' = K ⊔ τKτ⁻¹`

Then the HNN extension `HNN(↥K', A_{K'}, B_{K'}, φ_{K'})` of the pair `(K', τ)` is a *quotient* of
`HNN(↥K, A_K, B_K, φ_K)`:

  `HNN(K, τ) ↠ HNN(K', τ)`,  compatibly with the comparison maps to `G`.

Indeed `A_K = K ⊓ τ⁻¹Kτ` and `A_{K'} = K' ⊓ τ⁻¹K'τ`, and `K' = ⟨K, τKτ⁻¹⟩` forces
`K ⊆ A_{K'}` (since `K ⊆ K'` and `τKτ⁻¹ ⊆ K'`); so the *only* relations of the HNN of `K` (which
mention `A_K ⊆ A_{K'}`) are among the relations of the HNN of `K'`, and `HNN(K',τ)` is generated by
the images of `K` and of the stable letter.

**Consequence.**  If the comparison map of `(K, τ)` is injective and `G = ⟨K, τ⟩`, then so is the one
of `(K', τ)`: the composite `HNN(K,τ) ↠ HNN(K',τ) → G` is `hnnConjMap K τ`, an isomorphism, so
both maps are isomorphisms.

Iterating this along a chain `K₀ ≤ K₁ ≤ ⋯ ≤ K_N = H` with `K_{m+1} = K_m ⊔ τK_mτ⁻¹` reduces the
injectivity of `hnnConjMap H τ` to the injectivity of `hnnConjMap K₀ τ` for the *bottom* of the
chain.  For the band, the natural chain is `K_m = π₁(Y[0,m])` (or its mirror `π₁(Y[j,N])`); the
bottom of the chain is then a cyclic group. -/

set_option maxHeartbeats 1600000 in
open HNNExtension in
/-- **The climb.**  If `K' = ⟨K, τKτ⁻¹⟩` then the comparison map of the pair `(K', τ)` is a quotient
of that of `(K, τ)`, so its injectivity follows from the injectivity of `hnnConjMap K τ`. -/
theorem hnnConjMap_injective_of_sup_conj {G : Type*} [Group G] {K K' : Subgroup G} {τ : G}
    (hK : K ≤ K') (hconj : K.map (MulAut.conj τ) ≤ K')
    (hsup : K' ≤ K ⊔ K.map (MulAut.conj τ))
    (hinj : Function.Injective (hnnConjMap K τ)) :
    Function.Injective (hnnConjMap K' τ) := by
  classical
  have hgen : K' = K ⊔ K.map (MulAut.conj τ) := le_antisymm hsup (sup_le hK hconj)
  -- `K ≤ hnnEdgeA K' τ`
  have hA : ∀ a : ↥K, (a : G) ∈ hnnEdgeA K' τ := by
    intro a
    have h2 : τ * (a : G) * τ⁻¹ ∈ K' := hconj (Subgroup.mem_map.mpr ⟨(a : G), a.2, rfl⟩)
    rw [hnnEdgeA, Subgroup.mem_inf]
    refine ⟨hK a.2, Subgroup.mem_map.mpr ⟨τ * (a : G) * τ⁻¹, h2, ?_⟩⟩
    show (MulAut.conj τ⁻¹) (τ * (a : G) * τ⁻¹) = (a : G)
    rw [MulAut.conj_apply]
    group
  -- the map between the two HNN extensions
  let Ψ : HNNExtension ↥K ((hnnEdgeA K τ).subgroupOf K) ((hnnEdgeB K τ).subgroupOf K)
        (hnnConjEquiv K τ) →*
      HNNExtension ↥K' ((hnnEdgeA K' τ).subgroupOf K') ((hnnEdgeB K' τ).subgroupOf K')
        (hnnConjEquiv K' τ) :=
    HNNExtension.lift ((HNNExtension.of).comp (K.inclusion hK)) HNNExtension.t (by
      intro a
      -- the element `(a : ↥K)`, viewed in `↥K'`, lies in the associated subgroup of `K'`
      have hmem : ((⟨((a : ↥K) : G), hK (a : ↥K).2⟩ : ↥K')) ∈ (hnnEdgeA K' τ).subgroupOf K' :=
        Subgroup.mem_subgroupOf.mpr (hA (a : ↥K))
      let a' : (hnnEdgeA K' τ).subgroupOf K' :=
        ⟨⟨((a : ↥K) : G), hK (a : ↥K).2⟩, hmem⟩
      have hx : (a' : ↥K') = K.inclusion hK (a : ↥K) := rfl
      have hy : ((hnnConjEquiv K' τ a' : (hnnEdgeB K' τ).subgroupOf K') : ↥K')
          = K.inclusion hK (((hnnConjEquiv K τ a : (hnnEdgeB K τ).subgroupOf K)) : ↥K) := by
        refine Subtype.ext ?_
        show ((hnnConjEquiv K' τ a' : (hnnEdgeB K' τ).subgroupOf K') : G)
          = (((hnnConjEquiv K τ a : (hnnEdgeB K τ).subgroupOf K)) : G)
        rw [hnnConjEquiv_coe K' τ a', hnnConjEquiv_coe K τ a]
      conv_lhs => rw [MonoidHom.comp_apply, ← hx]
      conv_rhs => rw [MonoidHom.comp_apply, ← hy]
      exact HNNExtension.t_mul_of (φ := hnnConjEquiv K' τ) a')
  -- `of` of the two halves of a generating set of `K'` lies in the range of `Ψ`
  have hofK : ∀ y : ↥K', (y : G) ∈ K → HNNExtension.of y ∈ Ψ.range := by
    intro y hy
    refine ⟨HNNExtension.of (⟨(y : G), hy⟩ : ↥K), ?_⟩
    show HNNExtension.of (K.inclusion hK (⟨(y : G), hy⟩ : ↥K)) = HNNExtension.of y
    rfl
  have hofB : ∀ y : ↥K', (y : G) ∈ K.map (MulAut.conj τ) → HNNExtension.of y ∈ Ψ.range := by
    intro y hy
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
    have hky' : τ * k * τ⁻¹ = (y : G) := by
      have h := hky
      change (MulAut.conj τ) k = (y : G) at h
      rw [MulAut.conj_apply] at h
      exact h
    have hkA : (⟨k, hK hk⟩ : ↥K') ∈ (hnnEdgeA K' τ).subgroupOf K' :=
      Subgroup.mem_subgroupOf.mpr (hA ⟨k, hk⟩)
    let a' : (hnnEdgeA K' τ).subgroupOf K' := ⟨⟨k, hK hk⟩, hkA⟩
    have hrel := HNNExtension.equiv_eq_conj (φ := hnnConjEquiv K' τ) a'
    have hcoe : ((hnnConjEquiv K' τ a' : (hnnEdgeB K' τ).subgroupOf K') : ↥K') = y := by
      refine Subtype.ext ?_
      have h := hnnConjEquiv_coe K' τ a'
      rw [h]
      exact hky'
    have hofy : (HNNExtension.of ((hnnConjEquiv K' τ a' : (hnnEdgeB K' τ).subgroupOf K') : ↥K')
        : HNNExtension ↥K' ((hnnEdgeA K' τ).subgroupOf K') ((hnnEdgeB K' τ).subgroupOf K')
          (hnnConjEquiv K' τ)) = HNNExtension.of y := by rw [hcoe]
    have hofk : (HNNExtension.of (a' : ↥K')
        : HNNExtension ↥K' ((hnnEdgeA K' τ).subgroupOf K') ((hnnEdgeB K' τ).subgroupOf K')
          (hnnConjEquiv K' τ)) = HNNExtension.of (⟨k, hK hk⟩ : ↥K') := rfl
    rw [← hofy, hrel, ← hofk]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      ⟨HNNExtension.t, by simp only [Ψ, HNNExtension.lift_t]⟩ (hofK ⟨k, hK hk⟩ hk))
      (Subgroup.inv_mem _ ⟨HNNExtension.t, by simp only [Ψ, HNNExtension.lift_t]⟩)
  -- `↥K'` is generated by the two halves
  have htop : K.subgroupOf K' ⊔ (K.map (MulAut.conj τ)).subgroupOf K' = ⊤ := by
    have h1 : (K.subgroupOf K').map (Subgroup.subtype K') = K :=
      Subgroup.map_subgroupOf_eq_of_le hK
    have h2 : ((K.map (MulAut.conj τ)).subgroupOf K').map (Subgroup.subtype K')
        = K.map (MulAut.conj τ) := Subgroup.map_subgroupOf_eq_of_le hconj
    have h3 : (⊤ : Subgroup ↥K').map (Subgroup.subtype K') = K' := by
      rw [← Subgroup.subgroupOf_self K']
      exact Subgroup.map_subgroupOf_eq_of_le le_rfl
    apply Subgroup.map_injective (Subgroup.subtype_injective K')
    rw [Subgroup.map_sup, h1, h2, h3, hgen]
  have hofrange : (HNNExtension.of : ↥K' →* HNNExtension ↥K' ((hnnEdgeA K' τ).subgroupOf K')
      ((hnnEdgeB K' τ).subgroupOf K') (hnnConjEquiv K' τ)).range ≤ Ψ.range := by
    rintro x ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure ((((K.subgroupOf K' : Subgroup ↥K') : Set ↥K'))
        ∪ ((((K.map (MulAut.conj τ)).subgroupOf K' : Subgroup ↥K')) : Set ↥K')) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, htop]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact hofK y (Subgroup.mem_subgroupOf.mp hy)
        · exact hofB y (Subgroup.mem_subgroupOf.mp hy)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz => rw [map_mul]; exact Subgroup.mul_mem _ ihy ihz
    | inv y hy ihy => rw [map_inv]; exact Subgroup.inv_mem _ ihy
  -- `HNN(K', τ)` is generated by the image of `of` and the stable letter
  have hS : Subgroup.closure ((Set.range (HNNExtension.of : ↥K' →* HNNExtension ↥K'
      ((hnnEdgeA K' τ).subgroupOf K') ((hnnEdgeB K' τ).subgroupOf K') (hnnConjEquiv K' τ)))
        ∪ {HNNExtension.t}) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    refine HNNExtension.induction_on (A := (hnnEdgeA K' τ).subgroupOf K')
      (B := (hnnEdgeB K' τ).subgroupOf K') (φ := hnnConjEquiv K' τ) x ?_ ?_ ?_ ?_
    · intro g; exact Subgroup.subset_closure (Or.inl (Set.mem_range_self g))
    · exact Subgroup.subset_closure (Or.inr rfl)
    · intro a b ha hb; exact Subgroup.mul_mem _ ha hb
    · intro a ha; exact Subgroup.inv_mem _ ha
  have hsurj : Function.Surjective Ψ := by
    have hle : (⊤ : Subgroup (HNNExtension ↥K' ((hnnEdgeA K' τ).subgroupOf K')
        ((hnnEdgeB K' τ).subgroupOf K') (hnnConjEquiv K' τ))) ≤ Ψ.range := by
      rw [← hS]
      refine (Subgroup.closure_le (Ψ.range)).mpr ?_
      rintro x (⟨g, rfl⟩ | rfl)
      · exact hofrange ⟨g, rfl⟩
      · exact ⟨HNNExtension.t, by simp only [Ψ, HNNExtension.lift_t]⟩
    intro y
    exact hle (Subgroup.mem_top y)
  -- the two comparison maps agree through `Ψ`
  have hfac : (hnnConjMap K' τ).comp Ψ = hnnConjMap K τ := by
    refine HNNExtension.hom_ext ?_ ?_
    · ext k
      simp only [MonoidHom.comp_apply, Ψ, HNNExtension.lift_of, hnnConjMap_of,
        Subgroup.coe_inclusion]
    · simp only [MonoidHom.comp_apply, Ψ, HNNExtension.lift_t, hnnConjMap_t]
  intro x y hxy
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  have h : hnnConjMap K τ x' = hnnConjMap K τ y' := by
    rw [← DFunLike.congr_fun hfac x', ← DFunLike.congr_fun hfac y']
    exact hxy
  exact congrArg Ψ (hinj h)

/-- The `n`-fold iteration of the climb operation `K ↦ ⟨K, τKτ⁻¹⟩`: the chain of subgroups whose
injectivity of the comparison map is propagated by `hnnConjMap_injective_of_sup_conj`. -/
def conjChain {G : Type*} [Group G] (τ : G) : ℕ → Subgroup G → Subgroup G
  | 0, K => K
  | n + 1, K => conjChain τ n (K ⊔ K.map (MulAut.conj τ))

/-- **The chain corollary.**  If the comparison map of the pair `(K, τ)` is injective, then so is
that of `(conjChain τ n K, τ)`: the climb is iterated `n` times along the chain
`K_{j+1} = K_j ⊔ τK_jτ⁻¹`.  For the band, `K` is the bottom window `π₁(Y[0, p+q-1])` (a cyclic
group, for which injectivity is the Hopficity statement `freeGroup_two_gen`) and `conjChain τ n K`
is the band vertex `π₁(Y[0, p*q])` itself; the verification that the band's window chain *is* this
iteration is the remaining geometric input. -/
theorem hnnConjMap_injective_of_conjChain {G : Type*} [Group G] {K : Subgroup G} {τ : G}
    (hinj : Function.Injective (hnnConjMap K τ)) (n : ℕ) :
    Function.Injective (hnnConjMap (conjChain τ n K) τ) := by
  induction n generalizing K with
  | zero => exact hinj
  | succ n ih =>
      rw [conjChain]
      exact ih (hnnConjMap_injective_of_sup_conj le_sup_left le_sup_right le_rfl hinj)

/-- **The window subgroup** `π₁(Y[0,m])` of the band: the range of the class map `winRho` of the
window `[0,m]`.  For `m = p*q` this is the band vertex `tlH` (by definition, `tlH p q Wt =
tlWinWalk p q Wt (p*q)`), and the chain of these subgroups with

  `tlWinWalk p q Wt (m+1) = tlWinWalk p q Wt m ⊔ (tlWinWalk p q Wt m).map (MulAut.conj τ)`

is the chain to which `hnnConjMap_injective_of_conjChain` applies.  A machine-checked computation
(this session, Python) shows that the *inclusion* `τ · K_m · τ⁻¹ ≤ K_{m+1}` holds exactly when
`tlLowTauL ≤ m + 1`, and the *generation* requires the window intersection `[1,m]` to be connected
(`m ≥ p+q-1`); see `Submission/Work/OROneRel/NOTES_band_hnnConjMap_climb.md`, §1. -/
noncomputable def tlWinWalk (p q : ℕ) (Wt : ℤ → FreeGroup (Fin 2)) (m : ℤ) :
    Subgroup (FreeGroup (Fin 2)) :=
  (winRho Wt (tlW p q) 0 m).range

/-- The band vertex is the top of the window chain, by definition. -/
theorem tlH_eq_tlWinWalk (p q : ℕ) (Wt : ℤ → FreeGroup (Fin 2)) :
    tlH p q Wt = tlWinWalk p q Wt ((p : ℤ) * (q : ℤ)) := rfl

/-- **The gauge-free window subgroup** `π₁(Y[0,m])`: the elements of `F₂` representable by a walk of
the `tlW p q`-level graph staying inside the window `[0,m]`.  Unlike `tlWinWalk` this does **not**
depend on the choice of gauge, which is what makes the window *recursion*
`tlWin (m+1) = tlWin m ⊔ τ·tlWin m·τ⁻¹` true (see `Work.OROneRel.tlWin_succ` and
`NOTES_band_hnnConjMap_climb.md` §4.1: the corresponding statement for `tlWinWalk` is *false* for
gauges that merely satisfy `htree` on the whole band). -/
noncomputable def tlWin (p q : ℕ) (m : ℤ) : Subgroup (FreeGroup (Fin 2)) :=
  Subgroup.closure {x : FreeGroup (Fin 2) | ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = x ∧
    lsig (tlW p q) L = 0 ∧ ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m}

/-! ## §3.7 The two-generation criterion

The following observation turns the *target* into a statement with **no normal-form content**: if the
HNN extension of the pair `(H, τ)` (in `F₂`) is generated by two elements, and `H` together with `τ`
generates `F₂`, then `hnnConjMap H τ` is injective.

Indeed, a surjective hom `ρ : F₂ ↠ HNN(H, τ)` together with `σ := hnnConjMap H τ` (surjective, since
`⟨H, τ⟩ = F₂`) gives a *surjective* endomorphism `σ ∘ ρ` of `F₂`, hence an injective one by
`Work.OROneRel.freeGroup_fin_two_hopfian` (Hopfianity of `F₂`); and an injective composite with a
surjective first factor forces `σ` to be injective. -/
theorem hnnConjMap_injective_of_two_generated {H : Subgroup (FreeGroup (Fin 2))}
    {τ : FreeGroup (Fin 2)} (hgen : H ⊔ Subgroup.zpowers τ = ⊤)
    (u v : HNNExtension ↥H ((hnnEdgeA H τ).subgroupOf H) ((hnnEdgeB H τ).subgroupOf H)
      (hnnConjEquiv H τ))
    (h2 : Subgroup.closure ({u, v} : Set (HNNExtension ↥H ((hnnEdgeA H τ).subgroupOf H)
      ((hnnEdgeB H τ).subgroupOf H) (hnnConjEquiv H τ))) = ⊤) :
    Function.Injective (hnnConjMap H τ) := by
  classical
  let ρ : FreeGroup (Fin 2) →* HNNExtension ↥H ((hnnEdgeA H τ).subgroupOf H)
      ((hnnEdgeB H τ).subgroupOf H) (hnnConjEquiv H τ) :=
    FreeGroup.lift (fun i : Fin 2 => if i = 0 then u else v)
  have hρ : Function.Surjective ρ := by
    have hrange : ρ.range = ⊤ := by
      rw [eq_top_iff, ← h2]
      refine (Subgroup.closure_le ρ.range).mpr ?_
      rintro x (rfl | rfl)
      · exact MonoidHom.mem_range.mpr ⟨FreeGroup.of 0, by simp [ρ]⟩
      · exact MonoidHom.mem_range.mpr ⟨FreeGroup.of 1, by simp [ρ]⟩
    intro y
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top y)
  have hσ : Function.Surjective (hnnConjMap H τ) := by
    have hrange : (hnnConjMap H τ).range = ⊤ := by
      rw [eq_top_iff, ← hgen]
      refine sup_le ?_ ?_
      · intro h hh
        exact MonoidHom.mem_range.mpr ⟨HNNExtension.of ⟨h, hh⟩, by simp⟩
      · rw [Subgroup.zpowers_le]
        exact MonoidHom.mem_range.mpr ⟨HNNExtension.t, by simp⟩
    intro y
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top y)
  have hinjφ : Function.Injective ((hnnConjMap H τ).comp ρ) :=
    freeGroup_fin_two_hopfian _ (hσ.comp hρ)
  intro x y hxy
  obtain ⟨x', rfl⟩ := hρ x
  obtain ⟨y', rfl⟩ := hρ y
  have hx'y' : x' = y' := hinjφ hxy
  rw [hx'y']

/-- **The target from two-generation of the HNN of the band pair.**  This is
`hnnConjMap_injective_of_two_generated` instantiated at `H = tlH p q Wt`, `τ = tlTau p q`, using
`Work.OROneRel.twoLetter_F2_generation` for the generation hypothesis.  It exhibits the target's
remaining obligation as a statement with no normal-form content. -/
theorem band_hnnConjMap_injective_of_two_generated (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i)
      = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
        ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (u v : HNNExtension ↥(tlH p q Wt)
      ((hnnEdgeA (tlH p q Wt) (tlTau p q hp hq hcop)).subgroupOf (tlH p q Wt))
      ((hnnEdgeB (tlH p q Wt) (tlTau p q hp hq hcop)).subgroupOf (tlH p q Wt))
      (hnnConjEquiv (tlH p q Wt) (tlTau p q hp hq hcop)))
    (h2 : Subgroup.closure ({u, v} : Set (HNNExtension ↥(tlH p q Wt)
      ((hnnEdgeA (tlH p q Wt) (tlTau p q hp hq hcop)).subgroupOf (tlH p q Wt))
      ((hnnEdgeB (tlH p q Wt) (tlTau p q hp hq hcop)).subgroupOf (tlH p q Wt))
      (hnnConjEquiv (tlH p q Wt) (tlTau p q hp hq hcop)))) = ⊤) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlTau p q hp hq hcop)) := by
  have hgen : tlH p q Wt ⊔ Subgroup.zpowers (tlTau p q hp hq hcop) = ⊤ := by
    simpa only [tlH, tlTau, Subgroup.zpowers_eq_closure] using
      twoLetter_F2_generation p q hp hq hcop Wt hW0 hcoh hwin htree
  exact hnnConjMap_injective_of_two_generated hgen u v h2

/-- **The assembly of the climb.**  Given the window recursion
`tlWinWalk (m+1) = tlWinWalk m ⊔ τ·tlWinWalk m·τ⁻¹` for all `m ≥ m₀` (the statement
`Work.OROneRel.tlWinWalk_succ`) and the *bottom* case at `m₀` (`m₀` any integer at least
`max (p+q-1) (tlLowTauL - 1)` and at most `p*q`), the target follows: the chain of window subgroups
from `m₀` to `p*q` is exactly the iteration `conjChain τ · (tlWinWalk m₀)`, and its top is the band
vertex `tlH`. -/
theorem hnnConjMap_injective_of_winChain (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (m₀ : ℤ)
    (hrec : ∀ m : ℤ, m₀ ≤ m → m + 1 ≤ (p : ℤ) * (q : ℤ) →
      tlWinWalk p q Wt (m + 1) = tlWinWalk p q Wt m ⊔ (tlWinWalk p q Wt m).map
        (MulAut.conj (tlLowTau p q hp hq hcop)))
    (hN : m₀ ≤ (p : ℤ) * (q : ℤ))
    (hbot : Function.Injective
      (hnnConjMap (tlWinWalk p q Wt m₀) (tlLowTau p q hp hq hcop))) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)) := by
  set τ := tlLowTau p q hp hq hcop with hτ
  set n : ℕ := Int.toNat ((p : ℤ) * (q : ℤ) - m₀) with hn
  have hnonneg : 0 ≤ (p : ℤ) * (q : ℤ) - m₀ := by linarith
  have hmn : m₀ + (n : ℤ) = (p : ℤ) * (q : ℤ) := by
    rw [hn, Int.toNat_of_nonneg hnonneg]
    ring
  have hkey : ∀ j : ℕ, ∀ a : ℤ, m₀ ≤ a → a + (j : ℤ) ≤ (p : ℤ) * (q : ℤ) →
      conjChain τ j (tlWinWalk p q Wt a) = tlWinWalk p q Wt (a + (j : ℤ)) := by
    intro j
    induction j with
    | zero => intro a _ _; simp [conjChain]
    | succ j ih =>
        intro a ha hle
        rw [conjChain, ← hrec a ha (by push_cast at hle ⊢; linarith),
          ih (a + 1) (by linarith) (by push_cast at hle ⊢; linarith)]
        push_cast
        congr 1
        ring
  have htop : conjChain τ n (tlWinWalk p q Wt m₀) = tlH p q Wt := by
    rw [hkey n m₀ le_rfl (le_of_eq hmn), hmn, tlH_eq_tlWinWalk]
  rw [← htop]
  exact hnnConjMap_injective_of_conjChain hbot n

/-! ## §3.8 The **gauge-free** window-chain assembly

`hnnConjMap_injective_of_winChain` above uses the *gauge-dependent* window subgroups
`tlWinWalk p q Wt m = (winRho Wt (tlW p q) 0 m).range`, whose recursion is *false* for gauges that
only satisfy `htree` on the full band (see `NOTES_tlWinWalk_succ_FALSE.md`).  The correct object is
the gauge-free `tlWin p q m = π₁ (Y[0,m])` (the elements representable by a walk in the window
`[0,m]`), for which the recursion `tlWin (m+1) = tlWin m ⊔ τ·tlWin m·τ⁻¹` is the statement
`Work.OROneRel.tlWin_succ` — *verified to hold* in its exact hypothesis range
`max (p+q-1) (tlLowTauL - 1) ≤ m` (`NOTES_band_hnnConjMap_Tspace.md`, §1).

The following assembly lets the fleet consume `tlWin_succ` directly.  Its only extra input beyond
the recursion and the bottom case is the *top identification* `tlWin p q (p*q) = tlH p q Wt`, which
is `Work.OROneRel.tlWin_pq_eq_tlH` (proved in that module; it is passed as a hypothesis here so that
this file need not import it, which would be circular).

**Warning** (see `NOTES_band_hnnConjMap_Tspace.md`, §2): the recursion of `tlWin_succ` is only
available for `m ≥ tlLowTauL - 1 = p*q - max p q`, so the bottom level is
`m₀ = max (p+q, p*q - max p q) ≥ p+q`; the bottom window `tlWin p q m₀` therefore has rank
`m₀ - p - q + 2 ≥ 2` and is **never cyclic**.  The rank-one bottom case
(`Work.OROneRel.hnnConjMap_zpowers_injective`) cannot be used here: the chain reduces the target to
the *same* problem one window lower. -/
theorem hnnConjMap_injective_of_tlWin_chain (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (m₀ : ℤ)
    (htop : tlWin p q ((p : ℤ) * (q : ℤ)) = tlH p q Wt)
    (hrec : ∀ m : ℤ, m₀ ≤ m → m + 1 ≤ (p : ℤ) * (q : ℤ) →
      tlWin p q (m + 1) = tlWin p q m ⊔ (tlWin p q m).map
        (MulAut.conj (tlLowTau p q hp hq hcop)))
    (hN : m₀ ≤ (p : ℤ) * (q : ℤ))
    (hbot : Function.Injective
      (hnnConjMap (tlWin p q m₀) (tlLowTau p q hp hq hcop))) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)) := by
  set τ := tlLowTau p q hp hq hcop with hτ
  set n : ℕ := Int.toNat ((p : ℤ) * (q : ℤ) - m₀) with hn
  have hnonneg : 0 ≤ (p : ℤ) * (q : ℤ) - m₀ := by linarith
  have hmn : m₀ + (n : ℤ) = (p : ℤ) * (q : ℤ) := by
    rw [hn, Int.toNat_of_nonneg hnonneg]
    ring
  have hkey : ∀ j : ℕ, ∀ a : ℤ, m₀ ≤ a → a + (j : ℤ) ≤ (p : ℤ) * (q : ℤ) →
      conjChain τ j (tlWin p q a) = tlWin p q (a + (j : ℤ)) := by
    intro j
    induction j with
    | zero => intro a _ _; simp [conjChain]
    | succ j ih =>
        intro a ha hle
        rw [conjChain, ← hrec a ha (by push_cast at hle ⊢; linarith),
          ih (a + 1) (by linarith) (by push_cast at hle ⊢; linarith)]
        push_cast
        congr 1
        ring
  have htop' : conjChain τ n (tlWin p q m₀) = tlH p q Wt := by
    rw [hkey n m₀ le_rfl (le_of_eq hmn), hmn, htop]
  rw [← htop']
  exact hnnConjMap_injective_of_conjChain hbot n

/-! ## §4 The normal-form (Britton) statement for the band pair, and the reduction

`band_britton` is the statement that a chain-reduced word in the translated band vertices spells a
non-trivial element of `F₂`.  It is equivalent to the target (`band_britton` implies it by the
argument below, and it follows from it by Mathlib's Britton lemma
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`), so it is *true* — but it cannot be proved
from `(INT)` and the subgroup inclusions alone (§3bis of `band_cosetGraph_isTree.lean`); the
band-specific input is the slice structure of the band carrier (K),
`Work.OROneRel.tlBand_mul_inv_mem_tlH`.  The target is a formal consequence of `band_britton` and
Mathlib's reduced normal form of the HNN extension. -/

/-- **The normal-form (Britton) statement for the band pair `(H, τ)`.** -/
theorem band_britton (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {Wt : ℤ → FreeGroup (Fin 2)} (g₀ : FreeGroup (Fin 2)) (L : List (ℤˣ × FreeGroup (Fin 2)))
    (hg₀ : g₀ ∈ tlH p q Wt)
    (hL : ∀ i : Fin L.length, (L.get i).2 ∈ tlH p q Wt)
    (hchain : L.IsChain (fun a b => a.2 ∈ HNNExtension.toSubgroup
        (tlGateA p q hp hq hcop Wt) (tlGateB p q hp hq hcop Wt) a.1 → a.1 = b.1))
    (hprod : g₀ * (L.map (fun x : ℤˣ × FreeGroup (Fin 2) =>
        (tlTau p q hp hq hcop) ^ (x.1 : ℤ) * x.2)).prod = 1) :
    L = [] := by
  sorry

/-! ## §4.5 The target from the canonical "tree" crux

The remaining obligation is *exactly* the existence of the tree of the Bass--Serre structure of the
pair `(H₀, τ)`; in that form it is the statement `Work.OROneRel.winRhoRange_tree` of the workspace
(and the object of the whole fleet's `winRhoRange_tree` effort).  The passage
"tree-existence ⟹ injectivity of the comparison map" is *proved* in the workspace
(`Work.OROneRel.hnnConjMap_injective_of_tree`, via the Bass--Serre normal form
`Work.ORBassSerre.Action.Structure.hnn_reduced_word_ne_one`), so it only has to be instantiated.
See `Submission/Work/OROneRel/NOTES_band_hnnConjMap_state2.md` for the details and for the
independent verification that all the side hypotheses (stabilisers, no inversions, `τ • z = v`)
are satisfied by the band data. -/

/-- **The target from the tree-existence.**  If `F₂` acts on a tree without inversions with a
vertex `v` whose stabiliser is exactly the band vertex `H₀` and an edge `v ⟶ z` which is closed up
by `τ` (`τ • z = v`), then the comparison map of the pair `(H₀, τ)` is injective.  This is
`Work.OROneRel.hnnConjMap_injective_of_tree` with the stabiliser transported along
`Stab v = H₀`. -/
theorem band_hnnConjMap_injective_of_treeData (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2))
    (hT : ∃ (V : Type) (_ : Quiver V) (_ : Quiver.HasInvolutiveReverse V)
        (_ : MulAction (FreeGroup (Fin 2)) V)
        (_ : Work.ORBassSerre.GraphAction (FreeGroup (Fin 2)) V) (v z : V) (e : v ⟶ z),
        Work.ORBassSerre.IsTree V ∧
        Work.ORBassSerre.ActsWithoutInversions (FreeGroup (Fin 2)) V ∧
        MulAction.stabilizer (FreeGroup (Fin 2)) v = tlH p q Wt ∧
        (tlTau p q hp hq hcop) • z = v) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlTau p q hp hq hcop)) := by
  obtain ⟨V, hQ, hrev, hM, hGA, v, z, e, hTree, hninv, hstab, hclose⟩ := hT
  have h : Function.Injective
      (hnnConjMap (MulAction.stabilizer (FreeGroup (Fin 2)) v) (tlTau p q hp hq hcop)) :=
    hnnConjMap_injective_of_tree (G := FreeGroup (Fin 2)) hTree hninv v _ e hclose
  rwa [hstab] at h

theorem band_hnnConjMap_injective (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    Function.Injective (Work.OROneRel.hnnConjMap
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop)) := by
  -- `Work.OROneRel.band_hnnConjMap_injective_of_treeData` reduces this to the existence of the
  -- Bass--Serre tree of the pair `(H₀, τ)`, which is the statement
  -- `Work.OROneRel.winRhoRange_tree` (the fleet's crux).  It is the *only* remaining input:
  -- `exact band_hnnConjMap_injective_of_treeData p q hp hq hcop Wt (winRhoRange_tree …)`.
  sorry

end Work.OROneRel
