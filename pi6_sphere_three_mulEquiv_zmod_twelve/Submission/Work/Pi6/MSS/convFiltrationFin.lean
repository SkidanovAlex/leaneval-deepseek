import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

/-- One step of a descending induction on a filtration: if the term `A (t+1)` is finite
dimensional and the subquotient `A t / A (t+1)` is finite dimensional, then so is `A t`.

The hypothesis `hmono` is what identifies `Submodule.comap (A t).subtype (A (t+1))` with
`A (t+1)` (as a submodule of `↥(A t)`). -/
private theorem convFiltrationFin_step (𝕜 : Type) [Field 𝕜] (V : Type) [AddCommGroup V]
    [Module 𝕜 V] (A : ℕ → Submodule 𝕜 V) (hmono : ∀ t : ℕ, A (t+1) ≤ A t) (t : ℕ)
    (hnext : Module.Finite 𝕜 ↥(A (t+1)))
    (hgr : Module.Finite 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1)))) :
    Module.Finite 𝕜 ↥(A t) := by
  haveI := hnext
  haveI : Module.Finite 𝕜 ↥(Submodule.comap (A t).subtype (A (t+1))) :=
    Module.Finite.equiv
      (Submodule.comap_equiv_self_of_inj_of_le (f := (A t).subtype) (p := A (t+1))
        (Submodule.subtype_injective (A t))
        (by rw [Submodule.range_subtype]; exact hmono t)).symm
  haveI := hgr
  exact Module.Finite.of_submodule_quotient (Submodule.comap (A t).subtype (A (t+1)))

/-- Descending induction on the length `m` of the filtration. -/
private theorem convFiltrationFin_aux (𝕜 : Type) [Field 𝕜] (V : Type) [AddCommGroup V]
    [Module 𝕜 V] (m : ℕ) :
    ∀ A : ℕ → Submodule 𝕜 V, (∀ t : ℕ, A (t+1) ≤ A t) → A (m+1) = ⊥ →
      (∀ t : ℕ, t ≤ m →
        Module.Finite 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1)))) →
      Module.Finite 𝕜 ↥(A 0) := by
  induction m with
  | zero =>
    intro A hmono hbot hgr
    haveI : Module.Finite 𝕜 ↥(A (0+1)) := by rw [hbot]; infer_instance
    exact convFiltrationFin_step 𝕜 V A hmono 0 inferInstance (hgr 0 le_rfl)
  | succ m ih =>
    intro A hmono hbot hgr
    have h1 : Module.Finite 𝕜 ↥(A 1) :=
      ih (fun t => A (t+1)) (fun t => hmono (t+1)) (by simpa using hbot)
        (fun t ht => by
          have h := hgr (t+1) (Nat.succ_le_succ ht)
          simpa using h)
    exact convFiltrationFin_step 𝕜 V A hmono 0 h1 (hgr 0 (Nat.zero_le _))

theorem convFiltrationFin (𝕜 : Type) [Field 𝕜] (V : Type) [AddCommGroup V] [Module 𝕜 V]
    (A : ℕ → Submodule 𝕜 V) (hmono : ∀ t : ℕ, A (t+1) ≤ A t) (m : ℕ)
    (hbot : A (m+1) = ⊥)
    (hgr : ∀ t : ℕ, t ≤ m →
      Module.Finite 𝕜 (↥(A t) ⧸ Submodule.comap (A t).subtype (A (t+1)))) :
    Module.Finite 𝕜 ↥(A 0) :=
  convFiltrationFin_aux 𝕜 V m A hmono hbot hgr

end Work.Pi6.MSS
