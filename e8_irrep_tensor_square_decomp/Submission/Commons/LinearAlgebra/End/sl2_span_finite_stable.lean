import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Submission.Commons.Algebra.Lie.Sl2.uea_mul_pow
import Submission.Commons.Algebra.Lie.Sl2.pow_pow_eq_zero

namespace Commons.LinearAlgebra.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The one-step commutation relation `h f = f h - 2 f` in applied form. -/
lemma sl2_h_f_apply (h f : Module.End K V) (hhf : h * f - f * h = -((2:K) • f)) (u : V) :
    h (f u) = f (h u) - (2:K) • f u := by
  have h1 : h (f u) - f (h u) = -((2:K) • f u) := by
    have := congrArg (fun g : Module.End K V => g u) hhf
    simpa using this
  rw [sub_eq_add_neg, ← h1]
  abel

/-- The one-step commutation relation `h e = e h + 2 e` in applied form. -/
lemma sl2_h_e_apply (h e : Module.End K V) (hhe : h * e - e * h = (2:K) • e) (u : V) :
    h (e u) = e (h u) + (2:K) • e u := by
  have h1 : h (e u) - e (h u) = (2:K) • e u := by
    have := congrArg (fun g : Module.End K V => g u) hhe
    simpa using this
  rw [← h1]
  abel

/-- `h` acting on an `f`-string: `h (f^n w) = f^n (h w) - 2n • f^n w`. -/
lemma sl2_h_apply_pow_f (h f : Module.End K V) (hhf : h * f - f * h = -((2:K) • f))
    (n : ℕ) (w : V) :
    h ((f^n) w) = (f^n) (h w) + (-(((2*n:ℕ):K))) • ((f^n) w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have hL : h ((f ^ (n+1)) w) = f (h ((f^n) w)) - (2:K) • f ((f^n) w) := by
      simp only [pow_succ', Module.End.mul_apply, sl2_h_f_apply h f hhf]
    have hR : (f ^ (n+1)) (h w) + (-(((2*(n+1):ℕ):K))) • ((f ^ (n+1)) w)
        = f ((f^n) (h w)) + (-(((2*(n+1):ℕ):K))) • f ((f^n) w) := by
      simp only [pow_succ', Module.End.mul_apply]
    rw [hL, hR, ih w, map_add, map_smul]
    module

/-- `h` acting on an `e`-string: `h (e^n w) = e^n (h w) + 2n • e^n w`. -/
lemma sl2_h_apply_pow_e (h e : Module.End K V) (hhe : h * e - e * h = (2:K) • e)
    (n : ℕ) (w : V) :
    h ((e^n) w) = (e^n) (h w) + (((2*n:ℕ):K)) • ((e^n) w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have hL : h ((e ^ (n+1)) w) = e (h ((e^n) w)) + (2:K) • e ((e^n) w) := by
      simp only [pow_succ', Module.End.mul_apply, sl2_h_e_apply h e hhe]
    have hR : (e ^ (n+1)) (h w) + (((2*(n+1):ℕ):K)) • ((e ^ (n+1)) w)
        = e ((e^n) (h w)) + (((2*(n+1):ℕ):K)) • e ((e^n) w) := by
      simp only [pow_succ', Module.End.mul_apply]
    rw [hL, hR, ih w, map_add, map_smul]
    module

/-- The `e`-action on an `f`-string, from the associative-algebra form of the `𝔰𝔩₂` relation. -/
lemma sl2_e_mul_f_pow_apply (e f h : Module.End K V)
    (hef : e * f - f * e = h) (hhf : h * f - f * h = -((2:K) • f)) (n : ℕ) (w : V) :
    e ((f ^ (n + 1)) w)
      = (f ^ (n + 1)) (e w) + ((n + 1 : ℕ) : K) • ((f ^ n) ((h - (n:K) • 1) w)) := by
  have hEF : e * f = f * e + h := by
    calc e * f = (e * f - f * e) + f * e := by abel
      _ = h + f * e := by rw [hef]
      _ = f * e + h := by abel
  have hHF : h * f = f * h - (2:K) • f := by
    calc h * f = (h * f - f * h) + f * h := by abel
      _ = -((2:K) • f) + f * h := by rw [hhf]
      _ = f * h - (2:K) • f := by abel
  have key := Commons.Algebra.Lie.Sl2.uea_mul_pow_aux (R := K) (A := Module.End K V) e f h hEF hHF n
  have h2 := congrArg (fun g : Module.End K V => g w) key
  simpa [Module.End.mul_apply] using h2

/-- The `h`-action on a general `𝔰𝔩₂`-monomial `f^a e^b y`. -/
lemma sl2_h_f_pow_e_pow (h e f : Module.End K V) (hhe : h * e - e * h = (2:K) • e)
    (hhf : h * f - f * h = -((2:K) • f)) (a b : ℕ) (y : V) :
    h ((f^a) ((e^b) y))
      = (f^a) ((e^b) (h y)) + (((2*b:ℕ):K) - ((2*a:ℕ):K)) • ((f^a) ((e^b) y)) := by
  rw [sl2_h_apply_pow_f h f hhf a ((e^b) y), sl2_h_apply_pow_e h e hhe b y, map_add, map_smul]
  module

/-- **The `𝔰𝔩₂`-span of a finite-dimensional subspace is finite-dimensional and stable.**

Let `h e f` be endomorphisms of a vector space over a field `K` satisfying the three `𝔰𝔩₂`-relations
`h e - e h = 2 e`, `h f - f h = -2 f`, `e f - f e = h`, and suppose `e` and `f` are *locally
nilpotent*.  Let `W` be a finite-dimensional subspace stable under `h`, and let

  `M := span {f^a (e^b x) | a b : ℕ, x ∈ W}`

be the `𝔰𝔩₂`-span of `W`.  Then `M` is finite-dimensional and stable under `e`, `f` and `h`.

For the intended proof: `W` finite-dimensional and `e` locally nilpotent give a uniform bound
`e^B (W) = 0`, and for each `b < B` a uniform bound `f^{A_b} (e^b (W)) = 0`; hence
`M = span {f^a (e^b x) | x ∈ W, b < B, a < A_b}` is spanned by a finite set (take a basis of `W`).
Stability under `f` is immediate, stability under `h` follows from
`h (f^a e^b x) = f^a e^b (h x) + 2 (b - a) • f^a e^b x`, and stability under `e` from the
commutation relation `E F^a = F^a E + a • (F^{a-1} (H - (a-1)))` of
`Commons.Algebra.Lie.Sl2.uea_mul_pow` (the associative-algebra form `uea_mul_pow_aux` applies
directly to `Module.End K V`). -/
theorem sl2_span_finite_stable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (h e f : Module.End K V)
    (hhe : h * e - e * h = (2 : K) • e) (hhf : h * f - f * h = -((2 : K) • f))
    (hef : e * f - f * e = h)
    (he : ∀ v : V, ∃ n : ℕ, (e ^ n) v = 0) (hf : ∀ v : V, ∃ n : ℕ, (f ^ n) v = 0)
    (W : Submodule K V) [Module.Finite K ↥W] (hW : ∀ x ∈ W, h x ∈ W) :
    Module.Finite K ↥(Submodule.span K
        {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)}) ∧
      ∀ x ∈ Submodule.span K {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)},
        e x ∈ Submodule.span K {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)} ∧
        f x ∈ Submodule.span K {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)} ∧
        h x ∈ Submodule.span K {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)} := by
  classical
  let G : Set V := {y : V | ∃ (a b : ℕ) (x : V), x ∈ W ∧ y = (f ^ a) ((e ^ b) x)}
  let M : Submodule K V := Submodule.span K G
  change Module.Finite K ↥M ∧ ∀ x ∈ M, e x ∈ M ∧ f x ∈ M ∧ h x ∈ M
  -- every `𝔰𝔩₂`-monomial over `W` lies in `M`
  have hgen : ∀ (a b : ℕ) (y : V), y ∈ W → (f ^ a) ((e ^ b) y) ∈ M :=
    fun a b y hy => Submodule.subset_span ⟨a, b, y, hy, rfl⟩
  -- ## Finite dimensionality
  have hWfg : W.FG := (Submodule.fg_iff_finiteDimensional W).mpr inferInstance
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hWfg
  have hbdd : ∀ i : Fin n, ∃ N : ℕ, ∀ a b : ℕ, N ≤ a ∨ N ≤ b → (f ^ a) ((e ^ b) (s i)) = 0 :=
    fun i => Commons.Algebra.Lie.Sl2.pow_pow_eq_zero he hf (s i)
  choose N hN using hbdd
  let B : ℕ := Finset.univ.sup N + 1
  have hNB : ∀ i : Fin n, N i < B :=
    fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  let T : Set V := Set.range (fun p : Fin n × Fin B × Fin B =>
    (f ^ (p.2.1 : ℕ)) ((e ^ (p.2.2 : ℕ)) (s p.1)))
  have hTfin : T.Finite := Set.finite_range _
  have hTsubG : T ⊆ G := by
    rintro y ⟨p, rfl⟩
    exact ⟨(p.2.1 : ℕ), (p.2.2 : ℕ), s p.1,
      by rw [← hs]; exact Submodule.subset_span ⟨p.1, rfl⟩, rfl⟩
  have hG_le_T : G ⊆ Submodule.span K T := by
    rintro y ⟨a, b, x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        by_cases ha : a < B
        · by_cases hb : b < B
          · exact Submodule.subset_span ⟨(i, ⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
          · rw [hN i a b (Or.inr (le_trans (le_of_lt (hNB i)) (not_lt.mp hb)))]
            exact Submodule.zero_mem _
        · rw [hN i a b (Or.inl (le_trans (le_of_lt (hNB i)) (not_lt.mp ha)))]
          exact Submodule.zero_mem _
    | zero => simp
    | add u v _ _ ihu ihv => simp only [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul c u _ ihu => simp only [map_smul]; exact Submodule.smul_mem _ _ ihu
  have hM_eq : M = Submodule.span K T :=
    le_antisymm (Submodule.span_le.mpr hG_le_T)
      (Submodule.span_le.mpr fun y hy => Submodule.subset_span (hTsubG hy))
  have hMfg : M.FG := Submodule.fg_def.mpr ⟨T, hTfin, hM_eq.symm⟩
  have hfin : Module.Finite K ↥M := (Submodule.fg_iff_finiteDimensional M).mp hMfg
  -- ## Stability
  have he_mem : ∀ x ∈ M, e x ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, b, y, hy, rfl⟩ := hz
        rcases a with _ | a'
        · refine Submodule.subset_span (show e ((e ^ b) y) ∈ G from ⟨0, b + 1, y, hy, ?_⟩)
          simp only [pow_zero, Module.End.one_apply, pow_succ', Module.End.mul_apply]
        · rw [sl2_e_mul_f_pow_apply e f h hef hhf a' ((e ^ b) y)]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
          · refine Submodule.subset_span
              (show (f ^ (a' + 1)) (e ((e ^ b) y)) ∈ G from ⟨a' + 1, b + 1, y, hy, ?_⟩)
            simp only [pow_succ', Module.End.mul_apply]
          · have hinner : (h - (a' : K) • 1) ((e ^ b) y)
                = (e ^ b) (h y) + (((2 * b : ℕ) : K) - ((a' : ℕ) : K)) • ((e ^ b) y) := by
              simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
                sl2_h_apply_pow_e h e hhe b y]
              module
            rw [hinner, map_add, map_smul]
            exact Submodule.add_mem _
              (Submodule.subset_span
                (show (f ^ a') ((e ^ b) (h y)) ∈ G from ⟨a', b, h y, hW y hy, rfl⟩))
              (Submodule.smul_mem _ _
                (Submodule.subset_span (show (f ^ a') ((e ^ b) y) ∈ G from ⟨a', b, y, hy, rfl⟩)))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul c u _ ihu => rw [map_smul]; exact Submodule.smul_mem _ _ ihu
  have hf_mem : ∀ x ∈ M, f x ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, b, y, hy, rfl⟩ := hz
        refine Submodule.subset_span
          (show f ((f ^ a) ((e ^ b) y)) ∈ G from ⟨a + 1, b, y, hy, ?_⟩)
        simp only [pow_succ', Module.End.mul_apply]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul c u _ ihu => rw [map_smul]; exact Submodule.smul_mem _ _ ihu
  have hh_mem : ∀ x ∈ M, h x ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, b, y, hy, rfl⟩ := hz
        rw [sl2_h_f_pow_e_pow h e f hhe hhf a b y]
        exact Submodule.add_mem _
          (Submodule.subset_span
            (show (f ^ a) ((e ^ b) (h y)) ∈ G from ⟨a, b, h y, hW y hy, rfl⟩))
          (Submodule.smul_mem _ _
            (Submodule.subset_span (show (f ^ a) ((e ^ b) y) ∈ G from ⟨a, b, y, hy, rfl⟩)))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul c u _ ihu => rw [map_smul]; exact Submodule.smul_mem _ _ ihu
  exact ⟨hfin, fun x hx => ⟨he_mem x hx, hf_mem x hx, hh_mem x hx⟩⟩

end Commons.LinearAlgebra.End