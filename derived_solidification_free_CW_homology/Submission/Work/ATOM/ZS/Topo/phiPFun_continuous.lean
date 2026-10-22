import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

namespace Work.ATOM.ZS.Topo

/-- The fibre of `φ_P` over a finite point `j : ℕ`: `φ_P (k,j') = j` holds exactly for the points
`(k,j)` with `k ≤ n(j)`.  (In particular `φ_P` is `∞` on every point whose first coordinate is
`∞` or whose second coordinate is `∞`.) -/
lemma phiPFun_eq_some_iff (S : LightProfinite.{0}) [Infinite S] (j : ℕ)
    (p : ↥(Work.ATOM.NS2)) :
    Work.ATOM.phiPFun S p = (j : OnePoint ℕ) ↔
      ∃ k : ℕ, k ≤ Work.ATOM.lvl S j ∧ p = ((k : OnePoint ℕ), (j : OnePoint ℕ)) := by
  -- first reduce the claim to the case of two finite coordinates
  have key : ∀ k m : ℕ,
      Work.ATOM.phiPFun S ((k : OnePoint ℕ), (m : OnePoint ℕ)) = (j : OnePoint ℕ) ↔
      ∃ k' : ℕ, k' ≤ Work.ATOM.lvl S j ∧
        ((k : OnePoint ℕ), (m : OnePoint ℕ)) = ((k' : OnePoint ℕ), (j : OnePoint ℕ)) := by
    intro k m
    rw [Work.ATOM.phiPFun_some_some]
    by_cases h : k ≤ Work.ATOM.lvl S m
    · rw [ite_eq_left h]
      simp only [OnePoint.coe_eq_coe, Prod.mk.injEq]
      constructor
      · intro hj; exact ⟨k, hj ▸ h, rfl, hj⟩
      · rintro ⟨k', _hk', _h1', h2'⟩; exact h2'
    · rw [ite_eq_right h]
      simp only [Prod.mk.injEq, OnePoint.coe_eq_coe]
      constructor
      · intro hc; exact absurd hc (OnePoint.infty_ne_coe j)
      · rintro ⟨k', hk', h1', h2'⟩
        exact absurd ((h2'.symm ▸ (h1'.symm ▸ hk')) : k ≤ Work.ATOM.lvl S m) h
  by_cases h1 : p.1 = (∞ : OnePoint ℕ)
  · have hp : p = ((∞ : OnePoint ℕ), p.2) := Prod.ext h1 rfl
    rw [hp, Work.ATOM.phiPFun_infty_left]
    refine ⟨fun hc => absurd hc (OnePoint.infty_ne_coe j), ?_⟩
    rintro ⟨x, -, hx⟩
    exact absurd (congrArg Prod.fst hx) (OnePoint.infty_ne_coe x)
  · obtain ⟨k, hk⟩ := OnePoint.ne_infty_iff_exists.mp h1
    have hp : p = ((k : OnePoint ℕ), p.2) := Prod.ext hk.symm rfl
    rw [hp]
    by_cases h2 : p.2 = (∞ : OnePoint ℕ)
    · rw [h2, Work.ATOM.phiPFun_some_infty]
      refine ⟨fun hc => absurd hc (OnePoint.infty_ne_coe j), ?_⟩
      rintro ⟨x, -, hx⟩
      exact absurd (congrArg Prod.snd hx) (OnePoint.infty_ne_coe j)
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp h2
      rw [← hm]
      exact key k m

/-- Continuity of `φ_P : (ℕ∪{∞}) × (ℕ∪{∞}) ⟶ ℕ∪{∞}` (`Work.ATOM.phiPFun`).  Route: use the
criterion `Work.ATOM.continuous_onePoint_iff_isClopen`; the fibre over `j : ℕ` is
`{k | k ≤ n(j)} × {j}`, clopen because `{k : ℕ∪{∞} | k ≤ n(j)}` is finite (hence clopen) and
`{j}` is clopen in `ℕ∪{∞}`. -/
theorem phiPFun_continuous (S : LightProfinite.{0}) [Infinite S] :
    Continuous (Work.ATOM.phiPFun S) := by
  rw [Work.ATOM.continuous_onePoint_iff_isClopen]
  intro j
  -- the fibre over `j` is the finite union of the clopen boxes `{(k,j)}`, `k ≤ n(j)`
  have hset : Work.ATOM.phiPFun S ⁻¹' {(j : OnePoint ℕ)} =
      ⋃ k ∈ Set.Iic (Work.ATOM.lvl S j),
        (({(k : OnePoint ℕ)} : Set (OnePoint ℕ)) ×ˢ ({(j : OnePoint ℕ)} : Set (OnePoint ℕ))
          : Set ↥(Work.ATOM.NS2)) := by
    let F : ℕ → Set ↥(Work.ATOM.NS2) := fun k =>
      (({(k : OnePoint ℕ)} : Set (OnePoint ℕ)) ×ˢ ({(j : OnePoint ℕ)} : Set (OnePoint ℕ))
        : Set ↥(Work.ATOM.NS2))
    change Work.ATOM.phiPFun S ⁻¹' {(j : OnePoint ℕ)} = ⋃ k ∈ Set.Iic (Work.ATOM.lvl S j), F k
    ext p
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion₂]
    simp only [F, Set.mem_Iic]
    constructor
    · intro hp
      obtain ⟨k, hk, hpeq⟩ := (phiPFun_eq_some_iff S j p).mp hp
      exact ⟨k, hk, congrArg Prod.fst hpeq, congrArg Prod.snd hpeq⟩
    · rintro ⟨k, hk, h1, h2⟩
      exact (phiPFun_eq_some_iff S j p).mpr ⟨k, hk, Prod.ext h1 h2⟩
  rw [hset]
  exact Set.Finite.isClopen_biUnion (Set.finite_Iic _) fun k _ =>
    (Work.ATOM.isClopen_singleton_some k).prod (Work.ATOM.isClopen_singleton_some j)

end Work.ATOM.ZS.Topo
