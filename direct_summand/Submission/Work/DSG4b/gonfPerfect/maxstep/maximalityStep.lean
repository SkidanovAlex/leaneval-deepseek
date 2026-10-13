import Mathlib
import Submission.Work.DSG4b.gonfPerfect.pbAux

/-!
# The maximality step for `p`-bases

Let `L` be a field of characteristic a prime `p`, and let `L ^ p ⊆ L` be the subfield of `p`-th
powers.  A subset `S ⊆ L` is `p`-independent when the monomials `∏ a ^ (e a)` (exponents `< p`,
supported in `S`) are linearly independent over `L ^ p` (`pbAux.IsPIndep`).

This file proves `pbAux.MaximalityStep`: if `S` is `p`-independent but `S ∪ {x}` is not, then `x`
satisfies a nontrivial relation `∑_{k < p} A k · x ^ k = 0` whose coefficients `A k` all lie in the
subfield `pSpan L p S` (`= L ^ p[S]`, the `L ^ p`-span of the monomials over `S`, which is a field
by `pbAux.pSubfield`).

## Proof

Write a nontrivial `L ^ p`-linear dependence of the monomials over `insert x S` as
`∑_{e} g e · mon e = 0`.  Each exponent vector `e` supported in `insert x S` decomposes as
`e = (e - (e x) · δ_x) + (e x) · δ_x` with `e - (e x) · δ_x` supported in `S`, hence
`mon e = mon (e - (e x) · δ_x) · x ^ (e x)`.  Grouping the relation by the exponent `j = e x ∈ {0,…,
p-1}` produces `∑_{j < p} A j · x ^ j = 0` with
`A j = ∑_{e : e x = j} g e · mon (e - (e x) · δ_x) ∈ pSpan L p S`.
Some `A j` is nonzero: otherwise, for each `j`, `A j = 0` is an `L ^ p`-linear relation among the
monomials `mon (e - j · δ_x)`, which are `pMon`-values over the `p`-independent set `S`; comparing
the (injective!) family `e ↦ e - j · δ_x` with `pMon L p S` forces every `g e = 0`, contradicting
nontriviality of the relation.
-/

namespace Work.DSG4b.gonfPerfect.maxstep

open Work.DSG4b.gonfPerfect.pbAux

/-- Splitting a monomial according to the exponent at a single element `x`. -/
theorem mon_sub_single {L : Type*} [CommMonoid L] (e : L →₀ ℕ) (x : L) :
    mon e = mon (e - Finsupp.single x (e x)) * x ^ (e x) := by
  have hle : Finsupp.single x (e x) ≤ e := Finsupp.single_le_iff.mpr le_rfl
  have hv : e - Finsupp.single x (e x) + Finsupp.single x (e x) = e := tsub_add_cancel_of_le hle
  conv_lhs => rw [← hv]
  rw [mon_add, mon_single]

/-- Subtracting the exponent at `x` keeps the support inside `S` when the original support lies in
`insert x S`. -/
theorem rest_support {L : Type*} (S : Set L) (x : L) {e : L →₀ ℕ}
    (he : (e.support : Set L) ⊆ insert x S) :
    ((e - Finsupp.single x (e x)).support : Set L) ⊆ S := by
  intro y hy
  have hyne : (e - Finsupp.single x (e x)) y ≠ 0 := by
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hy
  have hyx : y ≠ x := by
    intro h
    subst h
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same, tsub_self] at hyne
    exact hyne rfl
  have hey : e y ≠ 0 := by
    intro h0
    rw [Finsupp.tsub_apply, h0, Finsupp.single_eq_of_ne hyx] at hyne
    simp at hyne
  have hmem : y ∈ insert x S :=
    he (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hey)
  rcases Set.mem_insert_iff.mp hmem with h | h
  · exact absurd h hyx
  · exact h

/-- Subtracting the exponent at `x` does not increase the exponents, so the `< p` bound persists. -/
theorem rest_lt {L : Type*} (p : ℕ) {e : L →₀ ℕ} (hp : ∀ a, e a < p) (x : L) :
    ∀ a, (e - Finsupp.single x (e x)) a < p := by
  intro a
  rw [Finsupp.tsub_apply]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (hp a)

/-- Grouping a sum over a finite set by the value of a map into `Fin p`, and pairing each group with
a power of `x`. -/
theorem sum_fiber_pairing {ι : Type*} {L : Type*} [CommSemiring L] (p : ℕ) (s : Finset ι)
    (f : ι → Fin p) (a : ι → L) (x : L) :
    ∑ k : Fin p, (∑ v ∈ s.filter (fun v => f v = k), a v) * x ^ (k : ℕ)
      = ∑ v ∈ s, a v * x ^ (f v : ℕ) := by
  calc ∑ k : Fin p, (∑ v ∈ s.filter (fun v => f v = k), a v) * x ^ (k : ℕ)
      = ∑ k : Fin p, ∑ v ∈ s.filter (fun v => f v = k), a v * x ^ (k : ℕ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ k : Fin p, ∑ v ∈ s.filter (fun v => f v = k), a v * x ^ (f v : ℕ) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun v hv => ?_)
        rw [Finset.mem_filter] at hv
        rw [hv.2]
    _ = ∑ v ∈ s, a v * x ^ (f v : ℕ) := Finset.sum_fiberwise s f (fun v => a v * x ^ (f v : ℕ))

/-- **The maximality step.**  If `S` is `p`-independent but `S ∪ {x}` is not, then `x` satisfies a
nontrivial relation of degree `< p` with coefficients in the subfield `pSpan L p S`. -/
theorem maximalityStep (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p] :
    Work.DSG4b.gonfPerfect.pbAux.MaximalityStep L p := by
  classical
  intro S x hS hns
  -- Unwrap the failure of `p`-independence of `insert x S` into a nontrivial relation.
  have hns' : ∃ (s : Finset (Idx L p (insert x S)))
      (g : Idx L p (insert x S) → pthPowerField L p),
      (∑ v ∈ s, g v • pMon L p (insert x S) v) = 0 ∧ ∃ u ∈ s, g u ≠ 0 := by
    rw [IsPIndep, linearIndependent_iff'] at hns
    push Not at hns
    exact hns
  obtain ⟨s, g, hsum, u, hu, hgu⟩ := hns'
  -- The exponent vector with the `x`-entry removed.
  let rest : Idx L p (insert x S) → L →₀ ℕ := fun v => v.1 - Finsupp.single x (v.1 x)
  have hrest_supp : ∀ v : Idx L p (insert x S), ((rest v).support : Set L) ⊆ S :=
    fun v => rest_support S x v.2.1
  have hrest_lt : ∀ (v : Idx L p (insert x S)) (a : L), rest v a < p :=
    fun v => rest_lt p v.2.2 x
  -- The `x`-exponent of `v`, as an element of `Fin p`.
  let fv : Idx L p (insert x S) → Fin p := fun v => ⟨v.1 x, v.2.2 x⟩
  -- The grouped coefficients `A k = ∑_{v : v x = k} g v · mon (rest v)`.
  let A : Fin p → L := fun k => ∑ v ∈ s.filter (fun v => fv v = k), (g v : L) * mon (rest v)
  have hA_mem : ∀ k, A k ∈ pSpan L p S := by
    intro k
    refine Submodule.sum_mem _ (fun v hv => ?_)
    have h1 : mon (rest v) ∈ pSpan L p S := mem_pSpan_of_mem S (hrest_supp v) (hrest_lt v)
    have h2 : (g v : L) * mon (rest v) = (g v) • mon (rest v) := by
      rw [Algebra.smul_def]
      rfl
    rw [h2]
    exact Submodule.smul_mem _ (g v) h1
  have hA_sum : ∑ k : Fin p, A k * x ^ (k : ℕ) = 0 := by
    rw [sum_fiber_pairing p s fv (fun v => (g v : L) * mon (rest v)) x]
    have h1 : ∀ v ∈ s, ((g v : L) * mon (rest v)) * x ^ ((fv v : ℕ)) = (g v : L) * mon v.1 := by
      intro v _
      rw [mon_sub_single v.1 x]
      ring
    rw [Finset.sum_congr rfl h1]
    rw [← hsum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Algebra.smul_def]
    rfl
  have hA_ne : ∃ k, A k ≠ 0 := by
    by_contra hc
    push Not at hc
    -- Restrict to the group of `v` with `v x = u x`.
    let t : Finset (Idx L p (insert x S)) := s.filter (fun v => fv v = fv u)
    let Φ : {v : Idx L p (insert x S) // v ∈ t} → Idx L p S :=
      fun v => ⟨rest v.1, hrest_supp v.1, hrest_lt v.1⟩
    have hinj : Function.Injective Φ := by
      intro a b hab
      have h1 : rest a.1 = rest b.1 := congrArg (fun w : Idx L p S => w.1) hab
      have ha : fv a.1 = fv u := (Finset.mem_filter.mp a.2).2
      have hb : fv b.1 = fv u := (Finset.mem_filter.mp b.2).2
      have hxa : a.1.1 x = b.1.1 x := by
        have : (fv a.1 : ℕ) = (fv b.1 : ℕ) := by rw [ha, hb]
        simpa using this
      apply Subtype.ext
      apply Subtype.ext
      have hle_a : Finsupp.single x (a.1.1 x) ≤ a.1.1 := Finsupp.single_le_iff.mpr le_rfl
      have hle_b : Finsupp.single x (b.1.1 x) ≤ b.1.1 := Finsupp.single_le_iff.mpr le_rfl
      calc a.1.1 = rest a.1 + Finsupp.single x (a.1.1 x) := (tsub_add_cancel_of_le hle_a).symm
        _ = rest b.1 + Finsupp.single x (b.1.1 x) := by rw [h1, hxa]
        _ = b.1.1 := tsub_add_cancel_of_le hle_b
    -- `A (u x) = 0` is a relation among the monomials over the `p`-independent `S`.
    have hli := hS.comp Φ hinj
    rw [linearIndependent_iff'] at hli
    have hu_t : u ∈ t := Finset.mem_filter.mpr ⟨hu, rfl⟩
    have hsum0 : (∑ v ∈ t.attach, g v.1 • pMon L p S (Φ v)) = 0 := by
      have e1 : (∑ v ∈ t.attach, g v.1 • pMon L p S (Φ v))
          = ∑ v ∈ t.attach, (g v.1 : L) * mon (rest v.1) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Algebra.smul_def]
        rfl
      have e2 : (∑ v ∈ t.attach, (g v.1 : L) * mon (rest v.1))
          = ∑ v ∈ t, (g v : L) * mon (rest v) :=
        Finset.sum_attach t (fun v => (g v : L) * mon (rest v))
      have e3 : (∑ v ∈ t, (g v : L) * mon (rest v)) = 0 := hc (fv u)
      rw [e1, e2]
      exact e3
    have hgu0 : g u = 0 :=
      hli t.attach (fun v => g v.1) hsum0 ⟨u, hu_t⟩ (Finset.mem_attach _ _)
    exact hgu hgu0
  exact ⟨A, hA_mem, hA_ne, hA_sum⟩

end Work.DSG4b.gonfPerfect.maxstep
