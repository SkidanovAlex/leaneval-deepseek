import Mathlib

open Finset

namespace Work.TMComp.IDSBox

theorem levelcount (g : ℝ → ℝ) (n : ℕ) (f : Fin n → ℝ) (s : Multiset ℝ)
    (hg : Antitone g)
    (hlev : ∀ m : Fin n, g (f m) = ((m : ℕ) : ℝ) + 1/2)
    (hnodup : s.Nodup)
    (hs : s.toFinset = Finset.univ.image f)
    (hb : ∀ X : ℝ, g X ∈ Set.Icc (0 : ℝ) (n : ℝ)) :
    ∀ X : ℝ, |((s.filter (fun r => r < X)).card : ℝ) - ((n : ℝ) - g X)| ≤ 2 := by
  classical
  intro X
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : g (f a) = g (f b) := by rw [hab]
    rw [hlev a, hlev b] at h
    have h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h')
  have hf_anti : Antitone f := by
    intro a b hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq; exact le_refl _
    · by_contra hcon
      rw [not_le] at hcon
      have h1 : g (f b) ≤ g (f a) := hg (le_of_lt hcon)
      rw [hlev a, hlev b] at h1
      have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
        have := Fin.lt_def.mp hlt
        exact_mod_cast this
      linarith
  have hcount : (s.filter (fun r => r < X)).card
      = (Finset.univ.filter (fun m : Fin n => f m < X)).card := by
    rw [← Multiset.toFinset_card_of_nodup (hnodup.filter (fun r => r < X)),
        Multiset.toFinset_filter, hs, Finset.filter_image,
        Finset.card_image_of_injective _ hf_inj]
  set A : Finset (Fin n) := Finset.univ.filter (fun m => f m < X) with hAdef
  set B : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (f m < X)) with hBdef
  have hAB : A.card + B.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun m => f m < X)
    simpa [hAdef, hBdef] using h
  have hta : (A.card : ℝ) ≤ (n : ℝ) - g X + 2 := by
    rcases A.eq_empty_or_nonempty with hAe | hAn
    · rw [hAe]; simp only [Finset.card_empty, Nat.cast_zero]
      have hle : g X ≤ (n : ℝ) := (hb X).2
      linarith
    · set j := A.min' hAn with hjdef
      have hjA : j ∈ A := Finset.min'_mem A hAn
      have hjmin : ∀ x ∈ A, j ≤ x := by
        intro x hx
        rw [hjdef]
        exact Finset.min'_le A x hx
      have hsub : A ⊆ Finset.Ici j := fun x hx => Finset.mem_Ici.mpr (hjmin x hx)
      have hcard : A.card ≤ n - j.val := by
        have h := Finset.card_le_card hsub
        rw [Fin.card_Ici] at h
        exact h
      have hjmem : j ∈ Finset.univ.filter (fun m : Fin n => f m < X) := by
        rw [← hAdef]; exact hjA
      have hjlt : f j < X := (Finset.mem_filter.mp hjmem).2
      have hgj : g X ≤ ((j : ℕ) : ℝ) + 1/2 := by
        have h : g X ≤ g (f j) := hg (le_of_lt hjlt)
        rwa [hlev j] at h
      have hjn : j.val ≤ n := le_of_lt j.isLt
      have hcardR : (A.card : ℝ) ≤ (n : ℝ) - (j.val : ℝ) := by
        have h1 : (A.card : ℝ) ≤ ((n - j.val : ℕ) : ℝ) := by exact_mod_cast hcard
        rwa [Nat.cast_sub hjn] at h1
      linarith [hcardR, hgj]
  have htb : (B.card : ℝ) ≤ g X + 2 := by
    rcases B.eq_empty_or_nonempty with hBe | hBn
    · rw [hBe]; simp only [Finset.card_empty, Nat.cast_zero]
      have h0 : (0:ℝ) ≤ g X := (hb X).1
      linarith
    · set k := B.max' hBn with hkdef
      have hkB : k ∈ B := Finset.max'_mem B hBn
      have hkmax : ∀ x ∈ B, x ≤ k := by
        intro x hx
        rw [hkdef]
        exact Finset.le_max' B x hx
      have hsub : B ⊆ Finset.Iic k := fun x hx => Finset.mem_Iic.mpr (hkmax x hx)
      have hcard : B.card ≤ k.val + 1 := by
        have h := Finset.card_le_card hsub
        rw [Fin.card_Iic] at h
        exact h
      have hkmem : k ∈ Finset.univ.filter (fun m : Fin n => ¬ (f m < X)) := by
        rw [← hBdef]; exact hkB
      have hkge : X ≤ f k := by
        have := (Finset.mem_filter.mp hkmem).2
        exact not_lt.mp this
      have hgk : ((k : ℕ) : ℝ) + 1/2 ≤ g X := by
        have h : g (f k) ≤ g X := hg hkge
        rwa [hlev k] at h
      have hcardR : (B.card : ℝ) ≤ (k.val : ℝ) + 1 := by
        have h1 : (B.card : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        push_cast at h1
        exact h1
      linarith [hcardR, hgk]
  have hcast : ((A.card : ℝ) + (B.card : ℝ)) = (n : ℝ) := by exact_mod_cast hAB
  rw [hcount]
  have hkey : ((Finset.univ.filter (fun m : Fin n => f m < X)).card : ℝ) - ((n : ℝ) - g X)
      = g X - (B.card : ℝ) := by
    have hA' : ((Finset.univ.filter (fun m : Fin n => f m < X)).card : ℝ) = (A.card : ℝ) := by
      rw [← hAdef]
    rw [hA']; linarith [hcast]
  rw [hkey, abs_le]
  constructor <;> linarith [hta, htb]

end Work.TMComp.IDSBox
