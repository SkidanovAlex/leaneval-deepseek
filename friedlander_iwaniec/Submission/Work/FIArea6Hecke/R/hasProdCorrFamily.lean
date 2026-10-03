import Mathlib

namespace Work.FIArea6Hecke.R

/-- The Euler-type product over all primes of the factor supported on the finite set `S`
(where `S` consists of primes) equals the finite product over `S`.

This is the "correlation family" local factor product: outside the finite set `S` of primes
the summand function is identically `1`, so the (unconditional) product over `Nat.Primes`
reduces to the finite product over `S`. -/
theorem hasProdCorrFamily (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (c₁ c₂ : ℕ → ℂ) (s : ℂ) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∈ S then
        (1 - c₁ (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))) * (1 - c₂ (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
      else 1)
      (∏ p ∈ S, (1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s)))) := by
  classical
  let f : Nat.Primes → ℂ := fun p => if (p : ℕ) ∈ S then
        (1 - c₁ (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))) * (1 - c₂ (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
      else 1
  let G : ℕ → ℂ := fun p => (1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s)))
  let g : {p // p ∈ S} → Nat.Primes := fun x => ⟨x.1, hS x.1 x.2⟩
  let sF : Finset Nat.Primes := S.attach.image g
  have h1 : ∀ b ∉ sF, f b = 1 := by
    intro b hb
    dsimp only [f]
    rw [if_neg]
    intro hbS
    exact hb (Finset.mem_image.mpr ⟨⟨(b : ℕ), hbS⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
  have h2 : (∏ b ∈ sF, f b) = ∏ p ∈ S, G p := by
    have hinj : Set.InjOn g ↑S.attach := by
      intro x _ y _ hxy
      have hxy' : (x : ℕ) = (y : ℕ) := by
        have h := congrArg (fun z : Nat.Primes => (z : ℕ)) hxy
        simpa [g] using h
      exact Subtype.ext hxy'
    have h3 : (∏ b ∈ sF, f b) = ∏ x ∈ S.attach, f (g x) := by
      dsimp only [sF]
      exact Finset.prod_image hinj
    rw [h3, ← Finset.prod_attach S G]
    apply Finset.prod_congr rfl
    intro x _
    dsimp only [f, G, g]
    rw [if_pos (show ((⟨x.1, hS x.1 x.2⟩ : Nat.Primes) : ℕ) ∈ S from x.2)]
  have key : HasProd f (∏ b ∈ sF, f b) :=
    hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Nat.Primes) h1
  rw [h2] at key
  exact key

end Work.FIArea6Hecke.R
