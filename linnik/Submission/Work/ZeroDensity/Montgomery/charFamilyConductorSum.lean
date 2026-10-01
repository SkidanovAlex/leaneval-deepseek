import Mathlib

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators

/-! ## Auxiliary facts about `changeLevel` and `conductor`

These small lemmas make the level bookkeeping of `DirichletCharacter.changeLevel`
(the proof-carrying transport of a Dirichlet character to a multiple level) usable
inside a `Finset.sum_bij` argument. -/

/-- `changeLevel` does not see the *proof* of the divisibility, only the levels: transporting the
character along an equality of levels commutes with `changeLevel`. -/
lemma changeLevel_cast {R : Type*} [CommMonoidWithZero R] {n m n' : ℕ} (hn : n = n')
    (h : n ∣ m) (h' : n' ∣ m) (χ : DirichletCharacter R n) :
    DirichletCharacter.changeLevel h' (hn ▸ χ) = DirichletCharacter.changeLevel h χ := by
  subst hn; congr 1

/-- Heterogeneous equality, transported to a genuine equality along the equality of the indices. -/
lemma cast_eq_of_heq {α : Sort*} {P : α → Sort*} {a b : α} (h : a = b) {x : P a} {y : P b}
    (hxy : HEq x y) : h ▸ x = y := by
  subst h
  exact eq_of_heq hxy

/-- The converse of `cast_eq_of_heq`. -/
lemma heq_of_cast_eq {α : Sort*} {P : α → Sort*} {a b : α} (h : a = b) {x : P a} {y : P b}
    (hxy : h ▸ x = y) : HEq x y := by
  subst h
  exact heq_of_eq hxy

/-- Lifting a primitive character mod `d` to a multiple level `q` keeps its conductor equal to `d`. -/
lemma conductor_changeLevel_of_isPrimitive {q d : ℕ} [NeZero q] (hd : d ∣ q)
    (χ' : DirichletCharacter ℂ d) (h : χ'.IsPrimitive) :
    (DirichletCharacter.changeLevel hd χ').conductor = d := by
  rw [DirichletCharacter.conductor_changeLevel χ' hd]
  exact (DirichletCharacter.isPrimitive_def χ').mp h

/-- The primitive character of a lift of a primitive character is the original character
(up to the identification of the two levels). -/
lemma primitiveCharacter_changeLevel_cast {q d : ℕ} [NeZero q] (hd : d ∣ q)
    (χ' : DirichletCharacter ℂ d) (h : χ'.IsPrimitive) :
    (conductor_changeLevel_of_isPrimitive hd χ' h) ▸
        (DirichletCharacter.changeLevel hd χ').primitiveCharacter = χ' := by
  apply DirichletCharacter.changeLevel_injective hd
  rw [changeLevel_cast (conductor_changeLevel_of_isPrimitive hd χ' h)
      (DirichletCharacter.conductor_dvd_level (DirichletCharacter.changeLevel hd χ')) hd
      ((DirichletCharacter.changeLevel hd χ').primitiveCharacter),
    DirichletCharacter.changeLevel_primitiveCharacter]

/-- The map `χ ↦ (χ.conductor, χ.primitiveCharacter)`, from characters mod `q` to the sigma type of
all characters indexed by a natural level, is injective. -/
lemma fwd_injective {q : ℕ} [NeZero q] :
    Function.Injective (fun χ : DirichletCharacter ℂ q =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Sigma (fun d => DirichletCharacter ℂ d))) := by
  intro χ₁ χ₂ h
  rw [Sigma.mk.inj_iff] at h
  obtain ⟨hc, hp⟩ := h
  have hpc : hc ▸ χ₁.primitiveCharacter = χ₂.primitiveCharacter := cast_eq_of_heq hc hp
  calc χ₁ = DirichletCharacter.changeLevel (DirichletCharacter.conductor_dvd_level χ₁)
              χ₁.primitiveCharacter :=
        (DirichletCharacter.changeLevel_primitiveCharacter χ₁).symm
    _ = DirichletCharacter.changeLevel (DirichletCharacter.conductor_dvd_level χ₂)
          (hc ▸ χ₁.primitiveCharacter) :=
        (changeLevel_cast hc (DirichletCharacter.conductor_dvd_level χ₁)
          (DirichletCharacter.conductor_dvd_level χ₂) χ₁.primitiveCharacter).symm
    _ = DirichletCharacter.changeLevel (DirichletCharacter.conductor_dvd_level χ₂)
          χ₂.primitiveCharacter := by rw [hpc]
    _ = χ₂ := DirichletCharacter.changeLevel_primitiveCharacter χ₂

/-- **Splitting the character family mod `q` by conductor.** Every `χ : DirichletCharacter ℂ q` equals `changeLevel` of its primitive character `χ.primitiveCharacter` modulo its conductor (`DirichletCharacter.changeLevel_primitiveCharacter`), and the map `χ ↦ (χ.conductor, χ.primitiveCharacter)` is a bijection onto the pairs `(d, χ')` with `d | q` and `χ'` a primitive character mod `d`. -/
theorem charFamilyConductorSum (q : ℕ) [NeZero q]
    (F : (d : ℕ) → DirichletCharacter ℂ d → ℝ) :
    (∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter)
      = ∑ d ∈ q.divisors, ∑ χ' : DirichletCharacter ℂ d,
          if χ'.IsPrimitive then F d χ' else 0 := by
  -- Rewrite the right-hand side as a single sum over the sigma type of pairs `(d, χ')`
  -- with `d ∈ q.divisors` and `χ'` a primitive character mod `d`.
  have hRHS : (∑ d ∈ q.divisors, ∑ χ' : DirichletCharacter ℂ d,
        if χ'.IsPrimitive then F d χ' else 0)
      = ∑ p ∈ q.divisors.sigma
          (fun d => Finset.univ.filter (fun χ' : DirichletCharacter ℂ d => χ'.IsPrimitive)),
          F p.1 p.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact (Finset.sum_filter (fun χ' : DirichletCharacter ℂ d => χ'.IsPrimitive)
      (fun χ' => F d χ')).symm
  rw [hRHS]
  -- Reindex the left-hand side by `χ ↦ (χ.conductor, χ.primitiveCharacter)`, which is a bijection
  -- onto the pairs above.
  refine Finset.sum_bij
    (fun (χ : DirichletCharacter ℂ q) (_ : χ ∈ Finset.univ) =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Sigma (fun d => DirichletCharacter ℂ d)))
    ?_ ?_ ?_ ?_
  · -- the image lies in the target Finset
    intro χ _
    rw [Finset.mem_sigma]
    exact ⟨Nat.mem_divisors.mpr ⟨DirichletCharacter.conductor_dvd_level χ, NeZero.ne q⟩,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, DirichletCharacter.primitiveCharacter_isPrimitive χ⟩⟩
  · -- injectivity
    intro a₁ _ a₂ _ h
    exact fwd_injective h
  · -- surjectivity
    intro b hb
    obtain ⟨d, χ'⟩ := b
    rw [Finset.mem_sigma] at hb
    obtain ⟨hdmem, hfilt⟩ := hb
    rw [Finset.mem_filter] at hfilt
    obtain ⟨_, hprim⟩ := hfilt
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hdmem).1
    exact ⟨DirichletCharacter.changeLevel hdvd χ', Finset.mem_univ _,
      Sigma.ext (conductor_changeLevel_of_isPrimitive hdvd χ' hprim)
        (heq_of_cast_eq (conductor_changeLevel_of_isPrimitive hdvd χ' hprim)
          (primitiveCharacter_changeLevel_cast hdvd χ' hprim))⟩
  · -- the two summands agree definitionally
    intro χ _
    rfl

end Work.ZeroDensity.Montgomery
