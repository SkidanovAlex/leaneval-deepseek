import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech

namespace Work.DSCOH

/-! ## Two bookkeeping lemmas for the proof of `cycle_piece_conditions`

* `sum_attach_eq_sum_dite` rewrites a sum over `s.attach` as a sum over `s` with an indicator
  (`dite`) factor; it is the tool that turns the `(T \ Z(β)).attach` sum of the statement into a
  sum over the finset `T \ Z(β)`.

* `cechCoeff_chart_congr` compares the coefficients of a Čech cochain at two *equal* charts
  (`S = T`): the chart localizations `locAt S` and `locAt T` are identified along the equality of
  the finsets, and the two pairings agree.  This is needed to compare the coefficient at the chart
  `(Z(β) ∪ {j}) \ {j}` with the coefficient at the chart `Z(β)` itself. -/

/-- A sum over the attached subtype is a sum over the finset with an indicator factor. -/
lemma sum_attach_eq_sum_dite {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (s : Finset α) (f : ∀ x, x ∈ s → M) :
    (∑ x ∈ s.attach, f x.1 x.2) = ∑ x ∈ s, if h : x ∈ s then f x h else 0 := by
  rw [← Finset.sum_attach s (fun x => if h : x ∈ s then f x h else 0)]
  exact Finset.sum_congr rfl fun x _ => (dif_pos x.2).symm

/-- **Change of chart.**  Reading the coefficient of the Čech cochain `a` in the bases `B S` and
`B T` gives the same result when `S = T`. -/
lemma cechCoeff_chart_congr {A : Type*} [CommRing A] {n : ℕ} {d q : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1))
    {S T : Finset (Fin n)} (h : S = T) (hS : S.card = q + 1 + 1) (hT : T.card = q + 1 + 1)
    (idxS : {γ : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ γ i})
    (idxT : {γ : Fin n → ℤ // ∀ i, i ∉ T → 0 ≤ γ i})
    (hidx : idxS.1 = idxT.1) :
    ((B S).repr (Subtype.val (a ⟨S, hS⟩))) idxS
      = ((B T).repr (Subtype.val (a ⟨T, hT⟩))) idxT := by
  subst h
  rw [Subtype.ext hidx]

theorem cycle_piece_conditions {A : Type*} [CommRing A] {n : ℕ} {d : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (q : ℕ) (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1))
    (ha : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) a = 0) :
    (∀ (β : Fin n → ℤ) (T : Finset (Fin n)) (hZT : ∀ i ∈ Zset β, i ∈ T) (hcardT : T.card = q + 3),
      ∑ i ∈ (T \ Zset β).attach,
        (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
          ((B (T.erase i.1)).repr
            (cechCoeff a (T.erase i.1)
              (card_erase_of_mem' (Finset.mem_sdiff.mp i.2).1 hcardT)))
          ⟨β, Zset_index_erase (fun i hi => hZT i hi) (Finset.mem_sdiff.mp i.2).1
            (Finset.mem_sdiff.mp i.2).2⟩) = 0) ∧
    (∀ (β : Fin n → ℤ) (hZ : (Zset β).card = q + 2) (hle : q + 3 ≤ n),
      ((B (Zset β)).repr (cechCoeff a (Zset β) (by omega))) ⟨β, Zset_valid_self β⟩ = 0) := by
  classical
  -- The first clause is the `β`-coordinate of the `T`-component of the cocycle condition
  -- `cechDiff a = 0`, read through `coord_cechDiff`.
  have h1 : ∀ (β : Fin n → ℤ) (T : Finset (Fin n)) (hZT : ∀ i ∈ Zset β, i ∈ T)
      (hcardT : T.card = q + 3),
      ∑ i ∈ (T \ Zset β).attach,
        (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
          ((B (T.erase i.1)).repr
            (cechCoeff a (T.erase i.1)
              (card_erase_of_mem' (Finset.mem_sdiff.mp i.2).1 hcardT)))
          ⟨β, Zset_index_erase (fun i hi => hZT i hi) (Finset.mem_sdiff.mp i.2).1
            (Finset.mem_sdiff.mp i.2).2⟩) = 0 := by
    intro β T hZT hcardT
    have hβT : ∀ i, i ∉ T → 0 ≤ β i := (Zset_subset_iff T β).mp hZT
    have hcardE : ∀ (x : Fin n) (hx : x ∈ T), (T.erase x).card = q + 1 + 1 :=
      fun x hx => card_erase_of_mem' hx hcardT
    -- the summand of the target sum
    let φ : ∀ x : Fin n, x ∈ T \ Zset β → A := fun x h =>
      (((-1 : ℤ) ^ ((T.filter (fun y => y < x)).card)) •
        ((B (T.erase x)).repr
          (cechCoeff a (T.erase x) (card_erase_of_mem' (Finset.mem_sdiff.mp h).1 hcardT)))
        ⟨β, Zset_index_erase (fun i hi => hZT i hi) (Finset.mem_sdiff.mp h).1
          (Finset.mem_sdiff.mp h).2⟩)
    -- the summand of `coord_cechDiff`
    let ψ : ∀ x : Fin n, x ∈ T → A := fun x h =>
      (((-1 : ℤ) ^ ((T.filter (fun y => y < x)).card)) •
        (if hβ : ∀ j, j ∉ T.erase x → 0 ≤ β j
         then ((B (T.erase x)).repr (Subtype.val (a ⟨T.erase x, hcardE x h⟩))) ⟨β, hβ⟩
         else 0))
    -- the `dite`-extensions of `φ` and `ψ` to all of `Fin n`
    let F : Fin n → A := fun x => if h : x ∈ T \ Zset β then φ x h else 0
    let G : Fin n → A := fun x => if h : x ∈ T then ψ x h else 0
    -- move the target sum to a sum over the finset `T \ Zset β`
    have hstep1 : (∑ i ∈ (T \ Zset β).attach, φ i.1 i.2) = ∑ x ∈ T \ Zset β, F x :=
      sum_attach_eq_sum_dite _ φ
    -- the terms outside `T \ Zset β` vanish
    have hF : (∑ x ∈ T \ Zset β, F x) = ∑ x ∈ T, F x := by
      refine Finset.sum_subset Finset.sdiff_subset (fun x hxT hxnotin => ?_)
      dsimp only [F]
      rw [dif_neg hxnotin]
    -- pointwise comparison of the two indicator functions on `T`
    have hFG : (∑ x ∈ T, F x) = ∑ x ∈ T, G x := by
      refine Finset.sum_congr rfl (fun x hxT => ?_)
      by_cases hxZ : x ∈ Zset β
      · -- `x ∈ Z(β)`: the left term has been dropped, and on the right the `dite` condition
        -- fails because `x ∉ T.erase x`
        dsimp only [F, G, φ, ψ]
        rw [dif_neg (fun h => (Finset.mem_sdiff.mp h).2 hxZ), dif_pos hxT]
        rw [dif_neg (fun hc => (not_le.mpr (mem_Zset.mp hxZ)) (hc x (Finset.notMem_erase x T)))]
        simp
      · -- `x ∉ Z(β)`: the `dite` condition holds and both sides are the `β`-coordinate of `a`
        -- at the chart `T.erase x`
        dsimp only [F, G, φ, ψ]
        rw [dif_pos (Finset.mem_sdiff.mpr ⟨hxT, hxZ⟩), dif_pos hxT]
        rw [dif_pos (Zset_index_erase (fun i hi => hZT i hi) hxT hxZ)]
        simp only [cechCoeff]
    -- move the `coord_cechDiff` sum to a sum over the finset `T`
    have hG : (∑ x ∈ T, G x) = ∑ x ∈ T.attach, ψ x.1 x.2 :=
      (sum_attach_eq_sum_dite T ψ).symm
    -- the cocycle condition
    have hcoord := coord_cechDiff (A := A) (n := n) B d hB2 (q + 1) a ⟨T, by omega⟩ ⟨β, hβT⟩
    have h0 : (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) a)
        ⟨T, by omega⟩ = 0 := by
      rw [ha]; rfl
    have hz : ((B T).repr (Subtype.val ((cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) (q + 1) a) ⟨T, by omega⟩))) ⟨β, hβT⟩ = 0 := by
      rw [h0]; simp
    have hCOORD : (∑ i ∈ T.attach, ψ i.1 i.2) = 0 := by
      convert (hcoord.symm.trans hz) using 1
    show (∑ i ∈ (T \ Zset β).attach, φ i.1 i.2) = 0
    rw [hstep1, hF, hFG, hG]
    exact hCOORD
  refine ⟨h1, ?_⟩
  -- The second clause: when `|Z(β)| = q + 2` and `q + 3 ≤ n`, extend `Z(β)` by one element `j`
  -- to a chart `T` of cardinality `q + 3`.  The first clause at `T` has a single term, at `j`,
  -- and this term is the desired coefficient at the chart `Z(β)` (up to the identified chart and
  -- the invertible sign `±1`).
  intro β hZ hle
  have hex : ∃ j : Fin n, j ∉ Zset β := by
    by_contra hc
    have hc' : ∀ j, j ∈ Zset β := fun j => by
      by_contra hmem
      exact hc ⟨j, hmem⟩
    rw [Finset.eq_univ_of_forall hc', Finset.card_univ, Fintype.card_fin] at hZ
    omega
  obtain ⟨j, hj⟩ := hex
  have hZT : ∀ i ∈ Zset β, i ∈ insert j (Zset β) := fun i hi => Finset.mem_insert_of_mem hi
  have hcardT : (insert j (Zset β)).card = q + 3 := by
    rw [Finset.card_insert_of_notMem hj, hZ]
  have herase : (insert j (Zset β)).erase j = Zset β := Finset.erase_insert hj
  have hp : j ∈ (insert j (Zset β)) \ Zset β :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self j (Zset β), hj⟩
  let φ : ∀ x : Fin n, x ∈ (insert j (Zset β)) \ Zset β → A := fun x h =>
    (((-1 : ℤ) ^ (((insert j (Zset β)).filter (fun y => y < x)).card)) •
      ((B ((insert j (Zset β)).erase x)).repr
        (cechCoeff a ((insert j (Zset β)).erase x)
          (card_erase_of_mem' (Finset.mem_sdiff.mp h).1 hcardT)))
      ⟨β, Zset_index_erase (fun i hi => hZT i hi) (Finset.mem_sdiff.mp h).1
        (Finset.mem_sdiff.mp h).2⟩)
  have hsum := h1 β (insert j (Zset β)) hZT hcardT
  have hsumφ : (∑ i ∈ ((insert j (Zset β)) \ Zset β).attach, φ i.1 i.2) = 0 := by
    convert hsum using 1
  -- the sum has the single term at `j`
  have hsingle : (∑ i ∈ ((insert j (Zset β)) \ Zset β).attach, φ i.1 i.2) = φ j hp := by
    have hmem : (⟨j, hp⟩ : {x : Fin n // x ∈ (insert j (Zset β)) \ Zset β}) ∈
        ((insert j (Zset β)) \ Zset β).attach := Finset.mem_attach _ _
    refine Finset.sum_eq_single
      (⟨j, hp⟩ : {x : Fin n // x ∈ (insert j (Zset β)) \ Zset β})
      (fun b _ hne => absurd ?_ hne) (fun h => absurd hmem h)
    apply Subtype.ext
    obtain ⟨hb1, hb2⟩ := Finset.mem_sdiff.mp b.2
    rcases Finset.mem_insert.mp hb1 with hh | hh
    · exact hh
    · exact absurd hh hb2
  have hzero : φ j hp = 0 := by rw [← hsingle]; exact hsumφ
  dsimp only [φ] at hzero
  simp only [cechCoeff] at hzero
  -- identify the chart `(Z(β) ∪ {j}) \ {j}` with the chart `Z(β)`
  rw [cechCoeff_chart_congr B a herase (card_erase_of_mem' (Finset.mem_sdiff.mp hp).1 hcardT)
      (show (Zset β).card = q + 1 + 1 by omega)
      ⟨β, Zset_index_erase (fun i hi => hZT i hi) (Finset.mem_sdiff.mp hp).1
        (Finset.mem_sdiff.mp hp).2⟩
      ⟨β, Zset_valid_self β⟩ rfl] at hzero
  -- the sign `(-1)^k` is invertible
  have hsgn2 : ((-1 : ℤ) ^ (((insert j (Zset β)).filter (fun x => x < j)).card)) *
      ((-1 : ℤ) ^ (((insert j (Zset β)).filter (fun x => x < j)).card)) = 1 := by
    rw [← mul_pow]; norm_num
  have hX : ((B (Zset β)).repr (cechCoeff a (Zset β) (by omega))) ⟨β, Zset_valid_self β⟩ = 0 := by
    have h2 := congrArg (fun y : A =>
      ((-1 : ℤ) ^ (((insert j (Zset β)).filter (fun x => x < j)).card)) • y) hzero
    rw [smul_smul, hsgn2, one_smul, smul_zero] at h2
    exact h2
  exact hX

end Work.DSCOH
