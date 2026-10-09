import Mathlib
import Submission.Work.SSGRoute.prop5.wtFiltration
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# wtz_filz_exists_pow  (ring bookkeeping)

**Statement.** If `a` has weight `≥ j+e` (a `p^s`-multiple of each length-`L` word with `s + L ≥ j+e`)
and length `≥ j`, then the degree-`j` part of `a` is `p^e · b`.

**Proof.** Generalise the PROVED `wtz_succ_le` / `wtz_filz_exists` (adjacent_pSeries_inter_lcs_le.lean,
the `e = 1` case) by induction on `e`, or directly by coefficients:
- `a ∈ wtz n` ⟺ every word `w` with `|w| ≥ 1` has coefficient divisible by `p^{n−|w|}`;
- take `b :=` (degree-`j` part of `a`) / `p^e`.

**Imports.** `prop5.wtFiltration`, `prop5.magnusFramework`. **Size.** Small.
-/

noncomputable section

open scoped commutatorElement BigOperators

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- `fil X j` is closed under integer multiples. -/
theorem int_smul_mem_fil_local (X : Type*) (j : ℕ) {f : FreeAssoc X} (hf : f ∈ fil X j) (c : ℤ) :
    c • f ∈ fil X j := by
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hf

/-- The length filtration is contained in the length-support submodule. -/
theorem fil_le_filz_local (X : Type*) (N : ℕ) : (fil X N : Set (FreeAssoc X)) ⊆ filz X N := by
  rw [fil_eq_filI]
  exact fun a ha => ha

/-- The generator case of `wtz_succ_le_local`. -/
theorem wtz_succ_le_gen_local (p : ℕ) (X : Type*) (j : ℕ) {c : FreeAssoc X}
    (hc : c ∈ wtSet p X (j + 1)) :
    ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1), c = (p : ℤ) • b + f := by
  obtain ⟨w, e, hw, hwe, rfl⟩ := hc
  by_cases hle : w.length ≤ j
  · have he : 1 ≤ e := by omega
    refine ⟨MonoidAlgebra.single w ((p : ℤ) ^ (e - 1)), ?_, 0, ?_, ?_⟩
    · exact single_mem_wtz (p := p) hw (e := e - 1) (by omega)
    · exact (fil X (j + 1)).zero_mem
    · rw [add_zero]
      rw [show (p : ℤ) • MonoidAlgebra.single w ((p : ℤ) ^ (e - 1))
          = MonoidAlgebra.single w ((p : ℤ) ^ e) from by
        rw [MonoidAlgebra.smul_single', ← pow_succ', show e - 1 + 1 = e from by omega]]
  · have hl : j + 1 ≤ w.length := by omega
    refine ⟨0, ?_, MonoidAlgebra.single w ((p : ℤ) ^ e), ?_, ?_⟩
    · exact (wtz p X j).zero_mem
    · rw [show MonoidAlgebra.single w ((p : ℤ) ^ e)
          = ((p : ℤ) ^ e) • MonoidAlgebra.single w 1 from by
        rw [MonoidAlgebra.smul_single', mul_one]]
      exact int_smul_mem_fil_local X (j + 1) (Ideal.subset_span ⟨w, hl, rfl⟩) ((p : ℤ) ^ e)
    · rw [smul_zero, zero_add]

/-- Every weight-`(j+1)` element is, modulo `fil X (j+1)`, `p` times a weight-`j` element. -/
theorem wtz_succ_le_local (p : ℕ) (X : Type*) (j : ℕ) {a : FreeAssoc X}
    (ha : a ∈ wtz p X (j + 1)) :
    ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1), a = (p : ℤ) • b + f := by
  refine Submodule.span_induction (p := fun a _ => ∃ b ∈ wtz p X j, ∃ f ∈ fil X (j + 1),
      a = (p : ℤ) • b + f) ?_ ?_ ?_ ?_ ha
  · exact fun c hc => wtz_succ_le_gen_local p X j hc
  · refine ⟨0, ?_, 0, ?_, ?_⟩
    · exact (wtz p X j).zero_mem
    · exact (fil X (j + 1)).zero_mem
    · rw [smul_zero, zero_add]
  · intro x y hx hy hpx hpy
    obtain ⟨b1, hb1, f1, hf1, rfl⟩ := hpx
    obtain ⟨b2, hb2, f2, hf2, rfl⟩ := hpy
    exact ⟨b1 + b2, Submodule.add_mem _ hb1 hb2, f1 + f2, Ideal.add_mem _ hf1 hf2, by
      rw [smul_add]; abel⟩
  · intro c x hx hpx
    obtain ⟨b, hb, f, hf, rfl⟩ := hpx
    exact ⟨c • b, Submodule.smul_mem _ c hb, c • f, int_smul_mem_fil_local X (j + 1) hf c, by
      rw [smul_add, smul_comm]⟩

/-- **Auxiliary form.** If `a` has weight `≥ j + e` and words of length `≥ j`, then
`a - p^e · b ∈ fil X (j+1)` for some `b` also supported in length `≥ j`. -/
theorem wtz_filz_exists_pow_aux (p : ℕ) (X : Type*) (j : ℕ) (hp : 0 < p) :
    ∀ e (a : FreeAssoc X), a ∈ wtz p X (j + e) → a ∈ filz X j →
      ∃ b ∈ filz X j, a - ((p : ℤ) ^ e) • b ∈ fil X (j + 1) := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hp)
  intro e
  induction e with
  | zero =>
      intro a ha haf
      exact ⟨a, haf, by simp⟩
  | succ e ih =>
      intro a ha haf
      have ha' : a ∈ wtz p X ((j + e) + 1) := by
        rwa [show j + (e + 1) = (j + e) + 1 from by omega] at ha
      obtain ⟨b₁, hb₁, f₁, hf₁, hab⟩ := wtz_succ_le_local p X (j + e) ha'
      have hb₁f : b₁ ∈ filz X j := by
        rw [mem_filz_iff] at haf ⊢
        intro w hw
        by_contra hlen
        have ha0 : a.coeff w = 0 := by
          by_contra hne
          exact absurd (haf w hne) (by omega)
        have hf0 : f₁.coeff w = 0 := by
          have hfz : f₁ ∈ filz X (j + e + 1) := fil_le_filz_local X (j + e + 1) hf₁
          rw [mem_filz_iff] at hfz
          by_contra hne
          exact absurd (hfz w hne) (by omega)
        have hpb : ((p : ℤ) • b₁).coeff w = 0 := by
          have h := congrArg (fun z : FreeAssoc X => z.coeff w) hab
          rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, ha0, hf0, add_zero] at h
          exact h.symm
        have hpb' : (p : ℤ) * b₁.coeff w = 0 := by
          rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hpb
          exact hpb
        rcases mul_eq_zero.1 hpb' with h | h
        · exact absurd h hpz
        · exact absurd h hw
      obtain ⟨b, hb, hbf⟩ := ih b₁ hb₁ hb₁f
      refine ⟨b, hb, ?_⟩
      have hpow : ((p : ℤ) ^ (e + 1)) • b = (p : ℤ) • (((p : ℤ) ^ e) • b) := by
        rw [pow_succ, mul_comm, smul_smul]
      have hsplit : a - ((p : ℤ) ^ (e + 1)) • b
          = (p : ℤ) • (b₁ - ((p : ℤ) ^ e) • b) + f₁ := by
        rw [hab, hpow, smul_sub]
        abel
      rw [hsplit]
      exact Ideal.add_mem _ (int_smul_mem_fil_local X (j + 1) hbf (p : ℤ))
        (fil_antitone X (by omega) hf₁)

end Work.SSGRoute.prop5

namespace Work.SSGRoute

open SSGRoute

theorem wtz_filz_exists_pow (p : ℕ) (X : Type) (j e : ℕ) (hp : 0 < p)
    {a : Work.SSGRoute.prop5.FreeAssoc X}
    (ha : a ∈ Work.SSGRoute.prop5.wtz p X (j + e)) (haf : a ∈ Work.SSGRoute.prop5.filz X j) :
    ∃ b ∈ Work.SSGRoute.prop5.filz X j,
      a - ((p : ℤ) ^ e) • b ∈ Work.SSGRoute.prop5.fil X (j + 1) :=
  Work.SSGRoute.prop5.wtz_filz_exists_pow_aux p X j hp e a ha haf

end Work.SSGRoute
