import Mathlib
import Submission.Work.Fatou.Surface.orbitDefs
import Submission.Work.Fatou.Qreg.fatouFundamental
import Submission.Work.Fatou.Qreg.fatouInjOnQ

/-!
# Two fundamental-strip representatives of the same orbit coincide

This file proves `Work.Fatou.Surface.meetFund`: the fundamental strip
`fundStrip F 𝒬 x₀ = {z ∈ 𝒬 | x₀ ≤ Re z ∧ every 𝒬-preimage of z has Re < x₀}` is a fundamental
domain for the orbit relation on `𝒬` — two points of the strip whose forward orbits meet inside `𝒬`
are equal, and the signed distance along the common orbit is determined.

The argument is a single reduction.  If `F^[a] s = F^[b] z` and `F^[a'] s' = F^[b'] z` with all
orbit pieces in `𝒬`, then (assuming `b ≤ b'`) the common point `F^[b] z` can be followed further
along the orbit of `s`, giving `F^[a + (b' - b)] s = F^[b'] z = F^[a'] s'` together with the
pieces `Piece F s (a + (b' - b))` and `Piece F s' a'` (`meet_piece_extend`).  Now two points of the
fundamental strip reach a common orbit point, with pieces inside `𝒬`; injectivity of the iterate
(`Work.Fatou.Surface.iter_injOn`) reduces this to the case where one of the two is itself an iterate
of the other, and `Work.Fatou.Surface.fund_iterate_eq` (no non-trivial forward iterate of a strip
point stays in the strip) forces the number of steps to vanish.  Hence `s = s'` and the two step
counts agree (`fund_eq_of_common`), which is exactly the equality of signed distances.

None of the three ingredients uses more than the defining geometry of the strip; no hypothesis on
the line `x₀` beyond membership in `fundStrip` is needed.
-/

namespace Work.Fatou.Surface

open Set Metric Complex MandelDim
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

section Extend

/-- **Continuing a common orbit.**  If the orbit of `s` meets the orbit of `z` inside `𝒬` at levels
`a` resp. `b`, then following the orbit of `z` for `n` further steps continues the orbit of `s`
identically: the piece of `s` extends to length `a + n` and `F^[a+n] s = F^[b+n] z`.

This is pure reindexing along a common orbit; it uses only that all the relevant `z`-iterates lie
in `𝒬`. -/
theorem meet_piece_extend {s z : ℂ} {a b n : ℕ} (hp : Piece b₁ b₂ F s a)
    (hp' : Piece b₁ b₂ F z (b + n)) (heq : F^[a] s = F^[b] z) :
    Piece b₁ b₂ F s (a + n) ∧ F^[a + n] s = F^[b + n] z := by
  constructor
  · intro j hj
    by_cases hja : j ≤ a
    · exact hp j hja
    · have haj : a ≤ j := le_of_lt (lt_of_not_ge hja)
      have h1 : F^[j] s = F^[j - a] (F^[a] s) := by
        conv_lhs => rw [show j = (j - a) + a from (Nat.sub_add_cancel haj).symm]
        exact Function.iterate_add_apply F (j - a) a s
      rw [h1, heq]
      have h2 : F^[j - a] (F^[b] z) = F^[(j - a) + b] z :=
        (Function.iterate_add_apply F (j - a) b z).symm
      rw [h2]
      exact hp' ((j - a) + b) (by omega)
  · have h1 : F^[a + n] s = F^[n] (F^[a] s) := by
      rw [show a + n = n + a from Nat.add_comm a n]
      exact Function.iterate_add_apply F n a s
    have h2 : F^[n] (F^[b] z) = F^[b + n] z := by
      rw [show b + n = n + b from Nat.add_comm b n]
      exact (Function.iterate_add_apply F n b z).symm
    rw [h1, heq, ← h2]

end Extend

section Uniqueness

/-- **The fundamental strip is a fundamental domain for the orbit relation.**  If two points `s`,
`s'` of the fundamental strip are both reached on a common orbit inside `𝒬` — `F^[N] s = F^[M] s'`
with both orbit pieces in `𝒬` — then `s = s'` and the two step counts agree, `N = M`.

Injectivity of the iterate on `𝒬` (`Work.Fatou.Surface.iter_injOn`) turns `F^[N] s = F^[M] s'`
(assuming `N ≤ M`) into `F^[M-N] s' = s`, and `Work.Fatou.Surface.fund_iterate_eq` — a non-trivial
forward iterate of a strip point whose piece stays in `𝒬` cannot land in the strip again — gives
`M - N = 0`. -/
theorem fund_eq_of_common {s s' : ℂ} {N M : ℕ}
    (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (hs' : s' ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (hp : Piece b₁ b₂ F s N) (hp' : Piece b₁ b₂ F s' M)
    (heq : F^[N] s = F^[M] s') : s = s' ∧ N = M := by
  rcases le_total N M with hNM | hMN
  · -- `N ≤ M`: from `s'` the common orbit point is reached in `N` steps as well
    have hpiece : Piece b₁ b₂ F (F^[M - N] s') N :=
      piece_of_iterate (by rw [Nat.sub_add_cancel hNM]; exact hp')
    have hinj : F^[M - N] s' = s := by
      refine iter_injOn hadm hF hpiece hp ?_
      rw [← Function.iterate_add_apply F N (M - N) s', Nat.add_sub_cancel' hNM]
      exact heq.symm
    obtain ⟨h0, heqs⟩ := fund_iterate_eq (s := s') (s' := s) (N := M - N) hF hs' hs
      (piece_mono hp' (Nat.sub_le M N)) hinj
    exact ⟨heqs.symm, by omega⟩
  · -- `M ≤ N`: symmetric
    have hpiece : Piece b₁ b₂ F (F^[N - M] s) M :=
      piece_of_iterate (by rw [Nat.sub_add_cancel hMN]; exact hp)
    have hinj : F^[N - M] s = s' := by
      refine iter_injOn hadm hF hpiece hp' ?_
      rw [← Function.iterate_add_apply F M (N - M) s, Nat.add_sub_cancel' hMN]
      exact heq
    obtain ⟨h0, heqs⟩ := fund_iterate_eq (s := s) (s' := s') (N := N - M) hF hs hs'
      (piece_mono hp (Nat.sub_le N M)) hinj
    exact ⟨heqs, by omega⟩

end Uniqueness

/-- **Two fundamental-strip representatives of the same orbit coincide.** If `s, s'` lie in the fundamental strip and both orbits meet the orbit of `z` inside `𝒬` (after `a` resp. `b` steps for `s`, and `a'` resp. `b'` steps for `s'`), then `s = s'` and the signed distances `a - b`, `a' - b'` agree. -/
theorem meetFund {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ} {s s' z : ℂ} {a b a' b' : ℕ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (hs' : s' ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀)
    (h : Work.Fatou.Surface.Meet b₁ b₂ F s z a b)
    (h' : Work.Fatou.Surface.Meet b₁ b₂ F s' z a' b') :
    s = s' ∧ ((a : ℤ) - (b : ℤ) = (a' : ℤ) - (b' : ℤ)) := by
  obtain ⟨heq, hps, hpz⟩ := h
  obtain ⟨heq', hps', hpz'⟩ := h'
  rcases le_total b b' with hbb | hb'b
  · -- `b ≤ b'`: continue the orbit of `s` along the orbit of `z` up to level `b'`
    have hpz'' : Piece b₁ b₂ F z (b + (b' - b)) := by rwa [Nat.add_sub_cancel' hbb]
    obtain ⟨hpiece, hval⟩ := meet_piece_extend hps hpz'' heq
    have hval' : F^[a + (b' - b)] s = F^[a'] s' := by
      rw [hval, Nat.add_sub_cancel' hbb, heq']
    obtain ⟨hss, hNM⟩ := fund_eq_of_common hadm hF hs hs' hpiece hps' hval'
    refine ⟨hss, ?_⟩
    have hsub : ((b' - b : ℕ) : ℤ) = (b' : ℤ) - (b : ℤ) := Nat.cast_sub hbb
    have hcast : ((a + (b' - b) : ℕ) : ℤ) = (a' : ℤ) := by rw [hNM]
    push_cast at hcast
    linarith
  · -- `b' ≤ b`: the same with the two representatives exchanged
    have hpz'' : Piece b₁ b₂ F z (b' + (b - b')) := by rwa [Nat.add_sub_cancel' hb'b]
    obtain ⟨hpiece, hval⟩ := meet_piece_extend hps' hpz'' heq'
    have hval' : F^[a' + (b - b')] s' = F^[a] s := by
      rw [hval, Nat.add_sub_cancel' hb'b, heq]
    obtain ⟨hss, hNM⟩ := fund_eq_of_common hadm hF hs' hs hpiece hps hval'
    refine ⟨hss.symm, ?_⟩
    have hsub : ((b - b' : ℕ) : ℤ) = (b : ℤ) - (b' : ℤ) := Nat.cast_sub hb'b
    have hcast : ((a' + (b - b') : ℕ) : ℤ) = (a : ℤ) := by rw [hNM]
    push_cast at hcast
    linarith

end

end Work.Fatou.Surface
