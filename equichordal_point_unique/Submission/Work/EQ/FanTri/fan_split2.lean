import Mathlib
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanTri.fan_split_defs
import Submission.Work.EQ.FanTri.fan_split
import Submission.Work.EQ.FanTri.decomp_spec
import Submission.Work.EQ.FanTri.dec_counts
import Submission.Work.EQ.FanTri.VisU_asm
import Submission.Work.EQ.FanTri.fVis_eq_VisU
import Submission.Work.EQ.FanTri.sgnAux_asm
import Submission.Work.EQ.FanTri.closed_word_trips
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.walk_bounds

namespace Work.EQ.FanTri

open Work.EQ Filter
open Classical

noncomputable section

/-! ## The weight extraction -/

/-- **A subsequence of closed words on which the signed weight is constant.**  Every closed word
is, by `decomp_spec`, a concatenation `asm L σ` of gaps and returning trips, and its signed
weight is the product `∏ τ ∈ σ, sgnAux a τ 0` of the weights of its trips (`sgnAux_asm`); the
gaps contribute `1` each, since the walk rests at `0` inside them (`sgW a true 0 = 1`).
`dec_counts` bounds the shape of `σ` by `VisU`, which is bounded by `N` here, so `σ` takes
finitely many values (`finite_bounded_trips`) and a subsequence has it constant. -/
theorem exists_subseq_sgnAux_const {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (C : ℕ → List Bool) (N : ℕ) (hclosed : ∀ k, stAux (C k) 0 = 0)
    (hN : ∀ k, VisU (C k) ≤ N) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ c : ℝ, ∀ k, sgnAux a (C (ψ k)) 0 = c := by
  classical
  have hspec : ∀ k, DecSpec (C k) (decomp (C k)).1 (decomp (C k)).2 :=
    fun k => decomp_spec (C k)
  have hb : ∀ k, ((decomp (C k)).2).length ≤ N ∧
      (((decomp (C k)).2).map List.length).sum ≤ 2 * N := by
    intro k
    obtain ⟨h1, h2⟩ := dec_counts (C k) (decomp (C k)).1 (decomp (C k)).2 (hspec k)
    exact ⟨le_trans h1 (hN k), le_trans h2 (Nat.mul_le_mul_left 2 (hN k))⟩
  have hfin : {p : List (List Bool) | p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N}.Finite := by
    refine (finite_bounded_trips N (2 * N)).subset ?_
    rintro p ⟨h1, h2⟩
    exact ⟨h1, fun τ hτ => by
      have h := List.le_sum_of_mem (xs := p.map List.length)
        (List.mem_map.mpr ⟨τ, hτ, rfl⟩)
      omega⟩
  haveI : Finite {p : List (List Bool) // p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N} :=
    hfin.to_subtype
  obtain ⟨t0, ψ, hψ, hσc⟩ := exists_const_subseq_of_finite
    (fun k => (⟨(decomp (C k)).2, hb k⟩ :
      {p : List (List Bool) // p.length ≤ N ∧ (p.map List.length).sum ≤ 2 * N}))
  refine ⟨ψ, hψ, (t0.val.map (fun τ => sgnAux a τ 0)).prod, fun k => ?_⟩
  have h2 : (decomp (C (ψ k))).2 = t0.val := congrArg Subtype.val (hσc k)
  have hlen : (decomp (C (ψ k))).1.length = t0.val.length + 1 := by
    rw [← h2]; exact (hspec (ψ k)).len
  have hcl := closed_word_trips (hclosed (ψ k)) (decomp (C (ψ k))).1
    (decomp (C (ψ k))).2 (hspec (ψ k))
  rw [h2] at hcl
  rw [(hspec (ψ k)).concat, h2]
  exact sgnAux_asm ha0 ha1 _ _ hlen hcl

end
/-- **Splitting a sequence of words with bounded walk visits, with a constant characteristic
weight.**  Let `ε : ℕ → List Bool` be a sequence of branch words with uniformly bounded walk visits,
`fVis (ε k) ≤ N`, and let `0 < a < 1` (the weights `sgW a` of `charValDefs.lean` are used).  Then
some subsequence is either constant, or has the form `ε₀ ++ trueˢᵏ ++ C k` with a fixed prefix `ε₀`,
a diverging run `s k → ∞` of principal steps, returning suffixes (`stAux (C k).reverse 0 = 0`, i.e.
`fan a h (C k) 0 = A₁` for any stable germ `h`) whose signed weight product
`Work.EQ.sgnAux a (C k).reverse 0` is *independent of `k`* — the extra conjunct beyond the plain
splitting lemma, needed because `charVal a h (C k) = sgnAux a (C k).reverse 0` for every word (the
`charVal` identity of `charVal_main`) and the trichotomy requires `charVal` to be constant along the
subsequence.

Why the constancy holds.  The level state satisfies `fLvl ε j = stp (ε[j]) (fLvl ε (j+1))` with
`fLvl ε |ε| = 0`, so the letters consumed at state `0` are exactly those of maximal runs of `true`
at state `0` (`stp true 0 = 0`), of which there are at most `N+1` since the state changes only at
the non-stationary steps (there are `fVis ε ≤ N` of them).  Hence
`ε = G₁ τ₁ G₂ τ₂ … τ_m G_{m+1}` with gaps `G_i = true^{g_i}` and trips `τ_i` (all of whose steps
but the last of each end off `0`); `Σ|τ_i| ≤ fVis ε + m ≤ 2N`, so after a subsequence all trips are
fixed and `m` is fixed.  For every level `j`,

`sgnAux a (C k).reverse 0 = ∏_{j = |ε₀| + s k}^{|ε(φ k)| - 1} sgW a (ε (φ k)[j]) (fLvl (ε (φ k)) (j+1))`,

and each factor inside a gap is `sgW a true 0 = -dnW a 0 = 1` (the level state is `0` throughout a
gap, and `dnW a 0 = -1` by `stQ a 0 = (1-a)/2`); inside a trip the level states are determined by
the trip alone, since a trip starts at state `0` (the preceding gap ends at `0`, and a gap is a
maximal run of `true` at state `0`).  So the product is independent of `k`: take `ε₁ := C k₀` for
any `k₀`.  The chosen gap is the *least* index `j` with `g_j` unbounded — the gaps before it are
bounded, hence constant on a further subsequence, so `ε₀ = G₁τ₁…τ_{j-1}` is fixed — and
`s k := g_j(k) - 1`, `C k := true ++ τ_j G_{j+1} … G_{m+1}`; the level walk is at state `0` at the
end of `ε₀` and a run of `true` from state `0` stays there, so `stAux (C k).reverse 0 = 0`.  If
every gap is bounded the words take finitely many values and the first disjunct holds. -/
theorem fan_split2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ε : ℕ → List Bool) (N : ℕ)
    (hN : ∀ k, Work.EQ.fVis (ε k) ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, ε (φ k) = ε₀) ∨
       ∃ (ε₀ : List Bool) (C : ℕ → List Bool) (s : ℕ → ℕ) (ε₁ : List Bool),
         Filter.Tendsto s Filter.atTop Filter.atTop ∧
         (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
         (∀ k, Work.EQ.stAux (C k).reverse 0 = 0) ∧
         Work.EQ.stAux ε₁.reverse 0 = 0 ∧
         (∀ k, Work.EQ.sgnAux a (C k).reverse 0 = Work.EQ.sgnAux a ε₁.reverse 0)) := by
  classical
  set u : ℕ → List Bool := fun k => (ε k).reverse with hu
  have hvis : ∀ k, VisU (u k) ≤ N := by
    intro k
    have h := fVis_eq_VisU (ε k)
    simp only [hu]
    rw [← h]
    exact hN k
  obtain ⟨φ, hφ, hres⟩ := fan_split_aux u N hvis
  rcases hres with ⟨v, hv⟩ | ⟨E, D, s, hsT, hdec, hD0⟩
  · refine ⟨φ, hφ, Or.inl ⟨v.reverse, fun k => ?_⟩⟩
    have h := hv k
    simp only [hu] at h
    rw [← h, List.reverse_reverse]
  · have hDvis : ∀ k, VisU (D k) ≤ N := by
      intro k
      have h1 : VisU (D k) ≤ VisU (D k ++ List.replicate (s k) true) :=
        VisU_le_append_left _ _
      have h2 : VisU (D k ++ List.replicate (s k) true)
          ≤ VisU (D k ++ List.replicate (s k) true ++ E) := VisU_le_append_left _ _
      have h3 : u (φ k) = D k ++ List.replicate (s k) true ++ E := hdec k
      calc VisU (D k) ≤ VisU (D k ++ List.replicate (s k) true ++ E) := le_trans h1 h2
        _ = VisU (u (φ k)) := by rw [h3]
        _ ≤ N := hvis (φ k)
    obtain ⟨ψ, hψ, c, hc⟩ := exists_subseq_sgnAux_const ha0 ha1 D N hD0 hDvis
    refine ⟨φ ∘ ψ, hφ.comp hψ,
      Or.inr ⟨E.reverse, fun k => (D (ψ k)).reverse, fun k => s (ψ k),
        (D (ψ 0)).reverse, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact hsT.comp hψ.tendsto_atTop
    · intro k
      have h := hdec (ψ k)
      simp only [hu] at h
      have h2 := congrArg List.reverse h
      simp only [List.reverse_append, List.reverse_replicate, List.reverse_reverse] at h2
      simpa using h2
    · intro k
      simpa [List.reverse_reverse] using hD0 (ψ k)
    · simpa [List.reverse_reverse] using hD0 (ψ 0)
    · intro k
      simpa [List.reverse_reverse] using (hc k).trans (hc 0).symm

end Work.EQ.FanTri
