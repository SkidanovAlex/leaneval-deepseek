import Submission.Work.Pi6.EMM2.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Dimension bookkeeping on the `E_2` page of a Serre spectral sequence (area EMM2)

For a Serre fibration `p : E → B` with finite type base and fibre over a field `𝕜`, this file
provides the dimension consequences of `IsSerreMSS` that the forcing arguments use:

* `e2_finrank`: `dim E_2^{s,q} = dim H^s(B) · dim H^q(F)`;
* `finrank_Einfinity_row0_le`: `dim E_{n+2}^{n,0} ≤ dim H^n(E)` (from `conv_dim`);
* `finrank_row0_bound`: the telescoped bound
  `dim H^n(B) ≤ dim H^n(E) + Σ_{q=1}^{n-1} dim H^{n-1-q}(B) · dim H^q(F)`.
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The fibre of `p` over its base point. -/
abbrev Fib (p : C(E, B)) (e₀ : E) : Type :=
  Work.StemsB.fibre p (p e₀)

instance (p : C(E, B)) (e₀ : E) : TopologicalSpace (Fib p e₀) :=
  inferInstanceAs (TopologicalSpace (Work.StemsB.fibre p (p e₀)))

/-- **The `E_2`-dimension is the product of base and fibre dimensions.** -/
theorem e2_finrank (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N)
    (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) :
    Module.finrank 𝕜 (S.E 2 ((s : ℤ), (q : ℤ))) =
      Module.finrank 𝕜 (Coh 𝕜 B s) * Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) q) := by
  obtain ⟨e2, _⟩ := hS
  rw [LinearEquiv.finrank_eq (e2 s q hs hq).toLinearEquiv]
  exact Module.finrank_tensorProduct

/-- **The page-`(n+2)` term in the row `q = 0` is at most `dim H^n(E)`.** -/
theorem finrank_Einfinity_row0_le (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hS : IsSerreMSS S p e₀ N) (n : ℕ) (hn : n ≤ N) :
    Module.finrank 𝕜 (S.E (n + 2) ((n : ℤ), (0 : ℤ))) ≤ Module.finrank 𝕜 (Coh 𝕜 E n) := by
  obtain ⟨_, _, _, hconv, _, _⟩ := hS
  rw [← hconv n hn]
  have h := Finset.single_le_sum (f := fun s : ℕ =>
    Module.finrank 𝕜 (S.E (n + 2) ((s : ℤ), ((n - s : ℕ) : ℤ)))) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega : n < n + 1))
  have h' : ((n - n : ℕ) : ℤ) = (0 : ℤ) := by simp
  rw [h'] at h
  exact h

/-- The dimension of `E_2^{n,0}`. -/
theorem e2_finrank_row0 (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N)
    (n : ℕ) (hn : n ≤ N) :
    Module.finrank 𝕜 (S.E 2 ((n : ℤ), (0 : ℤ))) =
      Module.finrank 𝕜 (Coh 𝕜 B n) * Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 0) :=
  e2_finrank S p e₀ N hS n 0 hn (by omega)

/-- The source bidegree of the `r`-th differential landing in the row `q = 0`, with natural
coordinates. -/
theorem sr_cast (n r : ℕ) (h : r + 2 ≤ n) :
    CohSS.sr n (r + 2) =
      (((n - (r + 2) : ℕ) : ℤ), (((r + 2) - 1 : ℕ) : ℤ)) := by
  ext
  · simp only [CohSS.sr, Prod.fst_sub, Prod.fst_ofNat, Nat.cast_sub h]
  · simp only [CohSS.sr, Prod.snd_sub, Prod.snd_ofNat, Nat.cast_sub (by omega : 1 ≤ r + 2)]
    norm_num

/-- **The telescoped dimension bound in the row `q = 0`.** -/
theorem finrank_row0_bound (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N)
    (hB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hF : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) q))
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 0) = 1)
    (n : ℕ) (hn : n ≤ N) :
    Module.finrank 𝕜 (Coh 𝕜 B n) ≤ Module.finrank 𝕜 (Coh 𝕜 E n) +
      ∑ r ∈ Finset.range (n - 1),
        Module.finrank 𝕜 (Coh 𝕜 B (n - (r + 2))) *
          Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) (r + 1)) := by
  -- finiteness of page `2` in the box `s + q ≤ N`
  have hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a) := by
    intro a h1 h2 h3
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a.1 = (m : ℤ) := ⟨a.1.toNat, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, a.2 = (q : ℤ) := ⟨a.2.toNat, by omega⟩
    have hmN : m ≤ N := by omega
    have hqN : q ≤ N := by omega
    obtain ⟨e2, _⟩ := hS
    haveI := hB m hmN
    haveI := hF q hqN
    have hpair : a = ((m : ℤ), (q : ℤ)) := by ext <;> simp [hm, hq]
    rw [hpair]
    exact Module.Finite.equiv (e2 m q hmN hqN).symm.toLinearEquiv
  have hmain := CohSS.finrank_row0_le S N hbox n hn
  rw [e2_finrank_row0 S p e₀ N hS n hn, hF0, mul_one] at hmain
  refine hmain.trans ?_
  have hinf := finrank_Einfinity_row0_le S p e₀ N hS n hn
  -- the sum: drop the last term (which is zero) and evaluate the others
  have hlast : Module.finrank 𝕜 (S.E 2 (CohSS.sr n ((n - 1) + 2))) = 0 := by
    have hneg : (CohSS.sr n ((n - 1) + 2)).1 < 0 ∨ (CohSS.sr n ((n - 1) + 2)).2 < 0 := by
      left
      simp only [CohSS.sr, Prod.fst_sub, Prod.fst_ofNat]
      omega
    exact S.finrank_eq_zero_of_neg (r := 2) hneg
  have hsplit : ∑ r ∈ Finset.range n, Module.finrank 𝕜 (S.E 2 (CohSS.sr n (r + 2))) =
      ∑ r ∈ Finset.range (n - 1), Module.finrank 𝕜 (S.E 2 (CohSS.sr n (r + 2))) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp
    · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      rw [show Finset.range n = Finset.range ((n - 1) + 1) from by rw [hn1],
        Finset.sum_range_succ, hlast, add_zero]
  rw [hsplit]
  refine add_le_add hinf (Finset.sum_le_sum ?_)
  intro r hr
  rw [Finset.mem_range] at hr
  have hr2 : r + 2 ≤ n := by omega
  have hidx : (r + 2) - 1 = r + 1 := by omega
  refine le_of_eq ?_
  rw [sr_cast n r hr2, hidx, e2_finrank S p e₀ N hS (n - (r + 2)) (r + 1)
    (by omega) (by omega)]

end

end Work.Pi6.EMM2
