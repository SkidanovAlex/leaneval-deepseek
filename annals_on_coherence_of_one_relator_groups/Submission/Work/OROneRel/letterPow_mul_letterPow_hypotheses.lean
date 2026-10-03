import Mathlib
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.rotate_flatten_replicate
import Submission.Work.OROneRel.isCyclicallyReducedRelator_of_pow
import Submission.Work.OROneRel.relatorNorm_letterPow_mul_letterPow
import Submission.Work.OROneRel.eps_letterPow_mul_letterPow
import Submission.Work.OROneRel.relatorLetters_letterPow_mul_letterPow
import Submission.Work.OROneRel.isCyclicallyReducedRelator_letterPow_mul_letterPow

namespace Work.OROneRel

/-- Two blocks of *distinct* generators concatenate to a reduced word. -/
theorem hyp_isReduced_replicate_append_replicate {α : Type*} {a b : α × Bool} (hab : a.1 ≠ b.1)
    (p q : ℕ) :
    FreeGroup.IsReduced (List.replicate p a ++ List.replicate q b) := by
  rw [FreeGroup.IsReduced, List.isChain_append]
  refine ⟨List.isChain_replicate_of_rel p (by simp),
          List.isChain_replicate_of_rel q (by simp), ?_⟩
  intro x hx y hy
  simp only [List.getLast?_replicate, List.head?_replicate, Option.mem_def] at hx hy
  split_ifs at hx hy
  all_goals (simp only [Option.some.injEq] at hx hy; subst hx; subst hy; simp_all)

/-- Two nonempty blocks of *distinct* generators concatenate to a cyclically reduced word. -/
theorem hyp_isCyclicallyReduced_replicate_append_replicate {α : Type*} {a b : α × Bool}
    (hab : a.1 ≠ b.1) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    FreeGroup.IsCyclicallyReduced (List.replicate p a ++ List.replicate q b) := by
  rw [FreeGroup.isCyclicallyReduced_iff]
  refine ⟨hyp_isReduced_replicate_append_replicate hab p q, ?_⟩
  intro x hx y hy
  have hp' : ¬ p = 0 := by omega
  have hq' : ¬ q = 0 := by omega
  rw [Option.mem_def] at hx hy
  rw [List.getLast?_append] at hx
  rw [List.head?_append] at hy
  simp only [List.getLast?_replicate] at hx
  simp only [List.head?_replicate] at hy
  rw [if_neg hq', if_neg hp'] at hx
  rw [if_neg hp', if_neg hq'] at hy
  simp only [Option.or_some, Option.some.injEq] at hx hy
  subst hx; subst hy
  intro h
  exact (hab h.symm).elim

/-- The reduced word of `(of a)^p * (of b)^q` for distinct generators `a ≠ b`. -/
theorem hyp_toWord_pow_mul_pow {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) (p q : ℕ) :
    FreeGroup.toWord ((FreeGroup.of a : FreeGroup α)^p * (FreeGroup.of b)^q)
      = List.replicate p (a, true) ++ List.replicate q (b, true) := by
  have hred : FreeGroup.IsReduced
      (List.replicate p ((a, true) : α × Bool) ++ List.replicate q (b, true)) :=
    hyp_isReduced_replicate_append_replicate (by simpa using hab) p q
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of_pow, FreeGroup.toWord_of_pow,
    hred.reduce_eq]

/-- **Combinatorial core.**  A word of the shape `a^p · b^q` (`p, q ≥ 1`, `a ≠ b`) cannot be a
nontrivial repetition of a nonempty block: there is no `V ≠ []` and `k ≥ 2` with
`a^p · b^q = V^k` (as reduced words over `α × Bool`).  Indeed such a representation makes the word
periodic of period `V.length`, forcing the letter at position `V.length` to be `(a, true)`, hence
`V.length < p`; then every letter of `V` is `(a, true)`, so `V^k` has no `b`-letter, while
`a^p b^q` does. -/
theorem not_flatten_replicate_eq_replicate_append {α : Type*} {a b : α} (hab : a ≠ b)
    {p q k : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hk : 2 ≤ k) {V : List (α × Bool)}
    (hVne : V ≠ [])
    (h : List.replicate p (a, true) ++ List.replicate q (b, true)
        = (List.replicate k V).flatten) :
    False := by
  classical
  have hmpos : 0 < V.length := List.length_pos_iff.mpr hVne
  have hkm : (List.replicate k V).flatten.length = k * V.length := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate, Nat.nsmul_eq_mul]
  have hlen : p + q = k * V.length := by
    have := congrArg List.length h
    rw [List.length_append, List.length_replicate, List.length_replicate, hkm] at this
    exact this
  have hmlt : V.length < p + q := by
    rw [hlen]
    calc V.length = 1 * V.length := (one_mul _).symm
      _ < k * V.length := Nat.mul_lt_mul_of_pos_right (by omega) hmpos
  -- periodicity of `W = a^p b^q` with period `V.length`
  have hper : ∀ i, i < k * V.length →
      (List.replicate p (a, true) ++ List.replicate q (b, true))[i]? = V[i % V.length]? := by
    intro i hi
    rw [h]
    exact Work.OROneRel.rfr_getElem?_flatten_replicate k V i (by rw [hkm]; exact hi)
  have h0 : (List.replicate p (a, true) ++ List.replicate q (b, true))[0]? = some (a, true) := by
    rw [List.getElem?_append, List.length_replicate, if_pos (by omega : 0 < p),
      List.getElem?_replicate, if_pos (by omega : 0 < p)]
  have hV0 : V[0]? = some (a, true) := by
    have hh := hper 0 (Nat.mul_pos (by omega : 0 < k) hmpos)
    rw [Nat.zero_mod] at hh
    rw [← hh, h0]
  have hVlen : (List.replicate p (a, true) ++ List.replicate q (b, true))[V.length]?
      = some (a, true) := by
    have hh := hper V.length (hlen ▸ hmlt)
    rw [Nat.mod_self] at hh
    rw [hh, hV0]
  have hVlen_lt_p : V.length < p := by
    by_contra hcon
    have hb : (List.replicate p (a, true) ++ List.replicate q (b, true))[V.length]?
        = some (b, true) := by
      rw [List.getElem?_append, List.length_replicate, if_neg (by omega : ¬ V.length < p),
        List.getElem?_replicate, if_pos (by omega : V.length - p < q)]
    rw [hVlen] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    exact hab hb.1
  have hV_small : ∀ i, i < V.length → V[i]? = some (a, true) := by
    intro i hi
    have hi' : i < k * V.length :=
      lt_of_lt_of_le hi (Nat.le_mul_of_pos_left _ (by omega : 0 < k))
    have hh := hper i hi'
    rw [Nat.mod_eq_of_lt hi] at hh
    rw [← hh]
    rw [List.getElem?_append, List.length_replicate, if_pos (by omega : i < p),
      List.getElem?_replicate, if_pos (by omega : i < p)]
  have hp_lt : p < k * V.length := by rw [← hlen]; omega
  have hWp_a : (List.replicate p (a, true) ++ List.replicate q (b, true))[p]?
      = some (a, true) := by
    have hh := hper p hp_lt
    rw [hh]
    exact hV_small (p % V.length) (Nat.mod_lt p hmpos)
  have hWp_b : (List.replicate p (a, true) ++ List.replicate q (b, true))[p]?
      = some (b, true) := by
    rw [List.getElem?_append, List.length_replicate, if_neg (by omega : ¬ p < p),
      List.getElem?_replicate, if_pos (by omega : p - p < q)]
  rw [hWp_b] at hWp_a
  simp only [Option.some.injEq, Prod.mk.injEq] at hWp_a
  exact hab hWp_a.1.symm

/-- `a^p · b^q` (`p, q ≥ 1`, `a ≠ b`) is never a proper power in the free group. -/
theorem not_isProperPower_letterPow_mul_letterPow {α : Type*} {a b : α} (hab : a ≠ b)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ¬ Work.OROneRel.IsProperPower ((FreeGroup.of a : FreeGroup α)^p * (FreeGroup.of b)^q) := by
  classical
  have hWdef := hyp_toWord_pow_mul_pow (α := α) hab p q
  have hcyc : Work.OROneRel.IsCyclicallyReducedRelator
      ((FreeGroup.of a : FreeGroup α)^p * (FreeGroup.of b)^q) := by
    have : FreeGroup.IsCyclicallyReduced
        (List.replicate p ((a, true) : α × Bool) ++ List.replicate q (b, true)) :=
      hyp_isCyclicallyReduced_replicate_append_replicate (by simpa using hab) hp hq
    unfold Work.OROneRel.IsCyclicallyReducedRelator
    rw [hWdef]
    exact this
  intro hpp
  obtain ⟨u, k, hk, hru⟩ := hpp
  have hcyc_u : Work.OROneRel.IsCyclicallyReducedRelator u :=
    isCyclicallyReducedRelator_of_pow u (by omega : 1 ≤ k) (hru ▸ hcyc)
  have hredV : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
    simpa only [Work.OROneRel.IsCyclicallyReducedRelator] using hcyc_u
  have hVne : FreeGroup.toWord u ≠ [] := by
    intro hnil
    have hu1 : u = 1 := FreeGroup.toWord_eq_nil_iff.mp hnil
    have h1 : FreeGroup.toWord ((FreeGroup.of a : FreeGroup α)^p * (FreeGroup.of b)^q) = [] := by
      rw [hru, hu1, one_pow, FreeGroup.toWord_one]
    rw [hWdef] at h1
    have hlen := congrArg List.length h1
    simp [List.length_replicate] at hlen
    omega
  have hflat : FreeGroup.toWord (u ^ k)
      = (List.replicate k (FreeGroup.toWord u)).flatten := by
    rw [FreeGroup.toWord_pow]
    exact (hredV.flatten_replicate k).1.reduce_eq
  have hmain : List.replicate p (a, true) ++ List.replicate q (b, true)
      = (List.replicate k (FreeGroup.toWord u)).flatten := by
    rw [← hWdef, hru, hflat]
  exact not_flatten_replicate_eq_replicate_append hab hp hq hk hVne hmain

theorem letterPow_mul_letterPow_hypotheses (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ¬ Work.OROneRel.IsProperPower
        ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q) ∧
      Work.OROneRel.IsCyclicallyReducedRelator
        ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q) ∧
      Work.OROneRel.relatorNorm
        ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q) = p + q ∧
      (∀ x : Fin 2, x ∈ Work.OROneRel.relatorLetters
          ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q) →
        Work.OROneRel.eps x
          ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q) ≠ 0) := by
  have hab : (0 : Fin 2) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact not_isProperPower_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab
      (by omega) (by omega)
  · exact isCyclicallyReducedRelator_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab
      (by omega) (by omega)
  · exact relatorNorm_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab p q
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := by
      have h := relatorLetters_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab p q hx
      simpa using h
    rcases hx' with rfl | rfl
    · have := (eps_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab p q).1
      rw [this]; omega
    · have := (eps_letterPow_mul_letterPow (a := (0 : Fin 2)) (b := 1) hab p q).2
      rw [this]; omega

end Work.OROneRel
