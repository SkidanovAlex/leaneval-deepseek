import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- **The ideal of denominators.**  Let `R` be a domain with fraction field `K`, and `f : K`.  If for
every maximal ideal `m` of `R` there are `s ∉ m` and `r : R` with `f * algebraMap R K s = algebraMap R K r` (i.e. `f` is regular at the localisation `R_m`), then `f` already lies in `R`.

Proof.  The set `I = {s : R | ∃ r : R, f * algebraMap R K s = algebraMap R K r}` is an ideal of `R`
(it contains `0`; it is closed under addition and under multiplication by elements of `R`).  If
`I ≠ ⊤` then `I` is contained in a maximal ideal `m`, but the hypothesis supplies `s ∈ I`, `s ∉ m`, a
contradiction.  Hence `I = ⊤`, so `1 ∈ I`, i.e. `f = algebraMap R K r` for some `r : R`. -/
theorem denominator_ideal_lift {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (f : K)
    (h : ∀ m : Ideal R, m.IsMaximal →
      ∃ s r : R, s ∉ m ∧ f * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, f = algebraMap R K r := by
  -- The ideal of "denominators" of `f`: the `s : R` for which `f * s` already lies in the image
  -- of `R` inside `K`.
  let I : Ideal R :=
    { carrier := {s : R | ∃ r : R, f * algebraMap R K s = algebraMap R K r}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨ra, ha⟩ ⟨rb, hb⟩
        exact ⟨ra + rb, by rw [map_add, mul_add, ha, hb, map_add]⟩
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        exact ⟨c * r, by rw [smul_eq_mul, map_mul, map_mul, mul_left_comm, hr]⟩ }
  -- If `I` were proper it would be contained in a maximal ideal `m`, and the hypothesis would
  -- supply `s ∈ I` with `s ∉ m`.
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, r, hs, hsr⟩ := h m hm
    exact hs (hle ⟨r, hsr⟩)
  -- Hence `1 ∈ I`, i.e. `f = algebraMap r`.
  obtain ⟨r, hr⟩ : (1 : R) ∈ I := (Ideal.eq_top_iff_one I).mp hI
  exact ⟨r, by simpa using hr⟩

end Work.MotV5
