import Mathlib
import Submission.Work.Peluse.Ulower.gcsStep
import Submission.Work.Peluse.Ulower.flatCubeSum
import Submission.Work.Peluse.Ulower.windowAggregate
import Submission.Work.Peluse.Ulower.chirpCS

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- `cornerShift v1 v0 ω` is the sum of the coordinates of `mix ω v0 v1`. -/
lemma peg_cornerShift_eq_sum_mix {s : ℕ} (v0 v1 : Fin s → ℤ) (ω : Fin s → Bool) :
    (∑ i : Fin s, (Concat.mix ω v0 v1) i) = cornerShift v1 v0 ω := rfl

/-- The `tsum` of a function supported in `[-M,M]` is the sum over `symIcc M`. -/
lemma peg_tsum_eq_sum_symIcc {G : ℤ → ℂ} {M : ℕ} (hG : SupportIn G M) :
    (∑' x : ℤ, G x) = ∑ x ∈ symIcc M, G x :=
  tsum_eq_sum (fun x hx => hG x (lt_natAbs_of_notMem_symIcc' hx))

/-- For `G t = f (x + t) * star (f (z + t))`, the flat cube product of `G` at the corners
`cornerShift v1 v0 ω` is `cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)`. -/
lemma peg_prod_G_eq (s : ℕ) (f : ℤ → ℂ) (v1 v0 : Fin s → ℤ) (x z : ℤ) :
    (∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
        ((fun t : ℤ => f (x + t) * star (f (z + t))) (cornerShift v1 v0 ω)))
      = cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z) := by
  simp only []
  rw [Concat.prod_star_pair]
  rfl

/-- The cube term of `G t = f (x + t) * star (f (z + t))` at `0` is the product of the cube terms
of `f` at `x` and the conjugate of the one at `z`. -/
lemma peg_cubeTerm_G_eq (s : ℕ) (f : ℤ → ℂ) (u : Fin s → ℤ) (w : Fin s → ℤ) (x z : ℤ) :
    cubeTerm u w (fun t : ℤ => f (x + t) * star (f (z + t))) 0
      = cubeTerm u w f x * star (cubeTerm u w f z) := by
  show (∏ β : Fin s → Bool, (star^[Work.Peluse.weight β])
      ((fun t : ℤ => f (x + t) * star (f (z + t))) (0 + cornerShift u w β)))
      = cubeTerm u w f x * star (cubeTerm u w f z)
  simp only [zero_add]
  rw [Concat.prod_star_pair]
  rfl

/-- The "`R`-sum" `∑_{v0,v1} cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)` is a nonnegative
real (it is the flat cube sum of the single function
`w ↦ f (x + ∑ i, w i) * star (f (z + ∑ i, w i))`). -/
lemma peg_R_isReal (s D : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) (f : ℤ → ℂ) (x z : ℤ) :
    (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z))
      = ((‖(∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z))‖ : ℝ) : ℂ) := by
  classical
  obtain ⟨r, hr0, hr⟩ := flatCubeSum_nonneg_finset (t := s) hs (arithIcc 1 D)
    (fun w : Fin s → ℤ => (fun t : ℤ => f (x + t) * star (f (z + t))) (∑ i : Fin s, w i))
  have hsum_eq : (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            ((fun w : Fin s → ℤ => (fun t : ℤ => f (x + t) * star (f (z + t)))
              (∑ i : Fin s, w i)) (Concat.mix ω v0 v1)))
      = (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)) := by
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    simp only [peg_cornerShift_eq_sum_mix]
    exact peg_prod_G_eq s f v1 v0 x z
  have h1 : (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)) = (r : ℂ) := by
    rw [← hsum_eq]; exact hr
  rw [h1]
  have hnorm : ‖((r : ℝ) : ℂ)‖ = r := by
    have hsq : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [hsq, norm_nonneg ((r : ℝ) : ℂ), hr0]
  exact congrArg (fun s : ℝ => (s : ℂ)) hnorm.symm

/-- **The `hflat` hypothesis applied at one point**: the flat cube sum of the cube terms of `f`
(with conjugated evaluation at `z`) is bounded by the flat cube sum of the cube terms at `x` and
`z` separately. -/
lemma peg_hflat_apply (s : ℕ) (hs : 1 ≤ s)
    (hflat : ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (h : Fin s → ℤ) (g : ℤ → ℂ),
        1 ≤ D → (∀ t : ℤ, ‖g t‖ ≤ 1) →
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm h (Concat.mix ω v0 v1) g 0)‖
        ≤ C * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (g (cornerShift v1 v0 ω))‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (f : ℤ → ℂ) (u : Fin s → ℤ) (x z : ℤ), 1 ≤ D → (∀ t : ℤ, ‖f t‖ ≤ 1) →
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x * star (cubeTerm u (Concat.mix ω v0 v1) f z))‖
        ≤ C * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖ := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hflat
  refine ⟨C₀, hC₀pos, ?_⟩
  intro D f u x z hD hf
  have hG1 : ∀ t : ℤ, ‖(fun t : ℤ => f (x + t) * star (f (z + t))) t‖ ≤ 1 := by
    intro t
    simp only []
    rw [norm_mul, norm_star]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  have key := hC₀ D u (fun t : ℤ => f (x + t) * star (f (z + t))) hD hG1
  have hL : (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            (cubeTerm u (Concat.mix ω v0 v1) (fun t : ℤ => f (x + t) * star (f (z + t))) 0))
      = (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x * star (cubeTerm u (Concat.mix ω v0 v1) f z))) := by
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    exact Finset.prod_congr rfl (fun ω _ =>
      congrArg (star^[Work.Peluse.weight ω])
        (peg_cubeTerm_G_eq s f u (Concat.mix ω v0 v1) x z))
  have hR : (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            ((fun t : ℤ => f (x + t) * star (f (z + t))) (cornerShift v1 v0 ω)))
      = (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)) := by
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    exact peg_prod_G_eq s f v1 v0 x z
  rw [hL, hR] at key
  exact key

/-! ## The exponential factor identities -/

lemma peg_star_exp (w : ℂ) : star (Complex.exp w) = Complex.exp (star w) := by
  simp only [Complex.star_def, ← Complex.exp_conj]

lemma peg_star_phase (θ : ℝ) :
    star (2 * Real.pi * Complex.I * (θ : ℂ)) = -(2 * Real.pi * Complex.I * (θ : ℂ)) := by
  rw [Complex.star_def]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma peg_exp_mul_star_exp (a ξ η : ℂ) (ha : star a = -a) (hη : star η = η) :
    Complex.exp (a * ξ) * star (Complex.exp (a * η)) = Complex.exp (a * (ξ - η)) := by
  rw [peg_star_exp, ← Complex.exp_add]
  congr 1
  have h1 : star (a * η) = -a * η := by rw [star_mul, ha, hη]; ring
  rw [h1]; ring

lemma peg_star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- Expanding the squared modulus of a finite sum. -/
lemma peg_sum_mul_star (S : Finset ℤ) (w : ℤ → ℂ) :
    (∑ x ∈ S, ∑ z ∈ S, w x * star (w z)) = ((‖∑ x ∈ S, w x‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ x : ℤ, (∑ z ∈ S, w x * star (w z)) = w x * star (∑ z ∈ S, w z) := by
    intro x
    rw [Concat.star_sum, Finset.mul_sum]
  have h2 : (∑ x ∈ S, ∑ z ∈ S, w x * star (w z)) = ∑ x ∈ S, w x * star (∑ z ∈ S, w z) :=
    Finset.sum_congr rfl (fun x _ => h1 x)
  rw [h2, ← Finset.sum_mul]
  simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj (∑ x ∈ S, w x)

/-- The pointwise exponential identity underlying the expansion of the chirped aggregate. -/
lemma peg_chirp_term_eq (s : ℕ) (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ)
    (u v : Fin s → ℤ) (f : ℤ → ℂ) (x z : ℤ) :
    cubeTerm u v f x * Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ)) *
        star (cubeTerm u v f z *
          Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (z : ℝ)))
      = cubeTerm u v f x * star (cubeTerm u v f z) *
        (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v) * ((x : ℝ) - (z : ℝ)))) := by
  have hstar_a : star (2 * Real.pi * Complex.I * (∑ i, ψ i u v))
      = -(2 * Real.pi * Complex.I * (∑ i, ψ i u v)) := peg_star_phase (∑ i, ψ i u v)
  have hcast : ((x : ℝ) : ℂ) - ((z : ℝ) : ℂ) = (((x : ℝ) - (z : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have hprod : Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ)) *
        star (Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (z : ℝ)))
      = ∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v) * ((x : ℝ) - (z : ℝ))) := by
    rw [peg_exp_mul_star_exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v)) ((x : ℝ) : ℂ) ((z : ℝ) : ℂ)
      hstar_a (peg_star_ofReal _)]
    rw [hcast, ← prod_exp_psi]
  calc cubeTerm u v f x * Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ)) *
        star (cubeTerm u v f z * Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (z : ℝ)))
      = cubeTerm u v f x * star (cubeTerm u v f z) *
          (Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ)) *
            star (Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (z : ℝ)))) := by
        rw [star_mul]; ring
    _ = cubeTerm u v f x * star (cubeTerm u v f z) *
          (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
            * ((x : ℝ) - (z : ℝ)))) := by rw [hprod]

/-- The chirped square sum of one pair of directions expands into the double sum over the window. -/
lemma peg_chirp_sq_expand (s L D : ℕ) (hD : 1 ≤ D) {f : ℤ → ℂ} (hsupp : SupportIn f L)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ) (u v : Fin s → ℤ)
    (hv : v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)) :
    ((‖∑' x : ℤ, cubeTerm u v f x *
        Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
          cubeTerm u v f x * star (cubeTerm u v f z) *
            (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
              * ((x : ℝ) - (z : ℝ)))) := by
  classical
  have hvD : ∀ i, (v i).natAbs ≤ D :=
    fun i => natAbs_le_of_mem_arithIcc (Fintype.mem_piFinset.mp hv i)
  have hsupp_c : SupportIn (cubeTerm u v f) (L + s * D) :=
    supportIn_cubeTerm (s := s) (L := L) (D := D) hsupp hvD
  have hsupp_w : SupportIn
      (fun x : ℤ => cubeTerm u v f x *
        Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))) (L + s * D) :=
    fun x hx => by show cubeTerm u v f x * _ = 0; rw [hsupp_c x hx, zero_mul]
  rw [peg_tsum_eq_sum_symIcc hsupp_w]
  rw [← peg_sum_mul_star]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  exact peg_chirp_term_eq s ψ u v f x z

/-- The chirped aggregate of the target is the triple sum of the GCS integrals. -/
lemma peg_chirped_expand (s L D : ℕ) (hD : 1 ≤ D) {f : ℤ → ℂ} (hsupp : SupportIn f L)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ) :
    ((∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ)))) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  exact peg_chirp_sq_expand s L D hD hsupp ψ u v hv

lemma peg_sum_comm4 {α β γ δ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (F : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d)
      = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d := by
  have h1 : ∀ a : α, (∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d)
      = ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, F a b c d := fun a => Finset.sum_comm
  have h2 : ∀ a : α, ∀ c : γ, (∑ b ∈ t, ∑ d ∈ v, F a b c d)
      = ∑ d ∈ v, ∑ b ∈ t, F a b c d := fun a c => Finset.sum_comm
  calc (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d)
      = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, F a b c d :=
        Finset.sum_congr rfl (fun a _ => h1 a)
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, F a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => h2 a c))
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, F a b c d := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

/-- The double sum expansion for an abstract family `T`. -/
lemma peg_double_sum_eq {s : ℕ} (S : Finset ℤ) (Qs : Finset (Fin s → ℤ))
    (T : (Fin s → ℤ) → (Fin s → ℤ) → ℤ → ℂ) :
    (∑ x ∈ S, ∑ z ∈ S, ∑ v0 ∈ Qs, ∑ v1 ∈ Qs, T v0 v1 x * star (T v0 v1 z))
      = ((∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ‖∑ x ∈ S, T v0 v1 x‖ ^ 2 : ℝ) : ℂ) := by
  have hper : ∀ v0 v1, (∑ x ∈ S, ∑ z ∈ S, T v0 v1 x * star (T v0 v1 z))
      = ((‖∑ x ∈ S, T v0 v1 x‖ ^ 2 : ℝ) : ℂ) :=
    fun v0 v1 => peg_sum_mul_star S (T v0 v1)
  calc (∑ x ∈ S, ∑ z ∈ S, ∑ v0 ∈ Qs, ∑ v1 ∈ Qs, T v0 v1 x * star (T v0 v1 z))
      = ∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ∑ x ∈ S, ∑ z ∈ S, T v0 v1 x * star (T v0 v1 z) :=
        peg_sum_comm4 S S Qs Qs (fun x z v0 v1 => T v0 v1 x * star (T v0 v1 z))
    _ = ∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ((‖∑ x ∈ S, T v0 v1 x‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => hper v0 v1))
    _ = ((∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ‖∑ x ∈ S, T v0 v1 x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun v0 _ => ?_)
        rw [Complex.ofReal_sum]

/-! ## The Gowers--Cauchy--Schwarz power step -/

lemma peg_gcsPow (s D : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) (f : ℤ → ℂ) (u : Fin s → ℤ)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ)
    (hind : ∀ i u v a b, ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) (x z : ℤ) :
    ‖∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        cubeTerm u v f x * star (cubeTerm u v f z) *
          (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
            * ((x : ℝ) - (z : ℝ))))‖ ^ 2 ^ s
      ≤ (D : ℝ) ^ (s * (2 ^ s - 2)) *
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x *
                star (cubeTerm u (Concat.mix ω v0 v1) f z))‖ := by
  classical
  have h1 := sum_piFinset_eq_sum_subtype' (arithIcc 1 D)
    (fun v : Fin s → ℤ => cubeTerm u v f x * star (cubeTerm u v f z) *
      (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
        * ((x : ℝ) - (z : ℝ)))))
  have hmix : ∀ (v0 v1 : Fin s → ↥(arithIcc 1 D)) (ω : Fin s → Bool),
      (fun i => (Concat.mix ω v0 v1 i).1)
        = Concat.mix ω (fun i => (v0 i).1) (fun i => (v1 i).1) := by
    intro v0 v1 ω
    funext i
    by_cases h : ω i = true <;> simp [Concat.mix, h]
  have h2 : (∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            (cubeTerm u (Concat.mix ω v0 v1) f x * star (cubeTerm u (Concat.mix ω v0 v1) f z)))
      = (∑ v0 : Fin s → ↥(arithIcc 1 D), ∑ v1 : Fin s → ↥(arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            (cubeTerm u (fun i => (Concat.mix ω v0 v1 i).1) f x *
              star (cubeTerm u (fun i => (Concat.mix ω v0 v1 i).1) f z))) := by
    rw [sum_piFinset₂_eq_sum_subtype']
    refine Finset.sum_congr rfl (fun v0 _ => Finset.sum_congr rfl (fun v1 _ => ?_))
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [← hmix v0 v1 ω]
  rw [h1, h2]
  have key := gcsStep s D hs hD f u ψ hind x z
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD0
  have h2pow : 2 ≤ 2 ^ s := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : (((D : ℝ)⁻¹) ^ s) ^ (2 ^ s) = ((D : ℝ)⁻¹) ^ (s * 2 ^ s) :=
    (pow_mul ((D : ℝ)⁻¹) s (2 ^ s)).symm
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast] at key
  rw [mul_pow] at key
  rw [hA] at key
  have hB : (D : ℝ) ^ (s * 2 ^ s) * ((D : ℝ)⁻¹) ^ (s * 2 ^ s) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hDne, one_pow]
  have hpow : (D : ℝ) ^ (s * 2 ^ s) * ((D : ℝ)⁻¹) ^ (2 * s) = (D : ℝ) ^ (s * (2 ^ s - 2)) := by
    rw [inv_pow, ← pow_sub₀ (D : ℝ) hDne (by
      calc 2 * s = s * 2 := by ring
        _ ≤ s * 2 ^ s := Nat.mul_le_mul_left s h2pow)]
    congr 1
    have h2s : 2 * s = s * 2 := by ring
    rw [h2s, Nat.mul_sub]
  have hpos : (0 : ℝ) ≤ (D : ℝ) ^ (s * 2 ^ s) := by positivity
  have hLeft : ∀ r : ℝ, (D : ℝ) ^ (s * 2 ^ s) * (((D : ℝ)⁻¹) ^ (s * 2 ^ s) * r) = r := by
    intro r
    rw [← mul_assoc, hB, one_mul]
  have hRight : ∀ r : ℝ, (D : ℝ) ^ (s * 2 ^ s) * (((D : ℝ)⁻¹) ^ (2 * s) * r)
      = (D : ℝ) ^ (s * (2 ^ s - 2)) * r := by
    intro r
    rw [← mul_assoc, hpow]
  have step := mul_le_mul_of_nonneg_left key hpos
  rw [hLeft, hRight] at step
  simpa only [Concat.mix] using step

/-! ## The Holder/cardinality step -/

lemma peg_sum_pow_le_card (s D : ℕ) (hD : 1 ≤ D) (S : Finset ℤ)
    (A : (Fin s → ℤ) → ℤ → ℤ → ℂ) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, A u x z‖ ^ p
      ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card * S.card ^ 2 : ℕ) : ℝ) ^ (p - 1)
        * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ p := by
  classical
  set P : ℝ := (p : ℝ) with hP
  have hP1 : 1 ≤ P := by rw [hP]; exact_mod_cast hp
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le zero_lt_one hP1
  have h1 : ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, A u x z‖
      ≤ ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun u _ => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
    exact norm_sum_le _ _
  have h2 : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖) ^ P
      ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ)) ^ (P - 1) *
        ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          (∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖) ^ P :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)) hP1
      (fun u _ => Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun z _ => norm_nonneg _)))
  have h3 : ∀ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      (∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖) ^ P
        ≤ ((S.card * S.card : ℕ) : ℝ) ^ (P - 1) * ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ P := by
    intro u _
    have hprod : (∑ q ∈ S.product S, ‖A u q.1 q.2‖) ^ P
        ≤ ((S.product S).card : ℝ) ^ (P - 1) * ∑ q ∈ S.product S, ‖A u q.1 q.2‖ ^ P :=
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (S.product S) hP1 (fun q _ => norm_nonneg _)
    simpa [Finset.sum_product, Finset.card_product] using hprod
  have step1 : ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, A u x z‖ ^ p
      = ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, A u x z‖ ^ P := by
    rw [hP, Real.rpow_natCast]
  rw [step1]
  have hsum_eq : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ P)
      = (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ p) := by
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun x _ =>
      Finset.sum_congr rfl (fun z _ => ?_)))
    rw [hP, Real.rpow_natCast]
  have hcoef : (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ)) ^ (P - 1)
        * ((S.card * S.card : ℕ) : ℝ) ^ (P - 1)
      = (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card * S.card ^ 2 : ℕ) : ℝ) ^ (p - 1) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    rw [← Nat.cast_mul]
    rw [show ((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card * (S.card * S.card) : ℕ)
        = (Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card * S.card ^ 2 by ring]
    rw [hP, ← Nat.cast_pred (by omega : 0 < p), Real.rpow_natCast]
  calc ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, A u x z‖ ^ P
      ≤ (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D), ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖) ^ P :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (le_of_lt hP0)
    _ ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ)) ^ (P - 1) *
        ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          (∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖) ^ P := h2
    _ ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ)) ^ (P - 1) *
        ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          (((S.card * S.card : ℕ) : ℝ) ^ (P - 1) * ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ P) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum h3) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) ^ (P - 1)
          * ((S.card * S.card : ℕ) : ℝ) ^ (P - 1)) *
        ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ P := by
        rw [← Finset.mul_sum]; ring
    _ = (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card * S.card ^ 2 : ℕ) : ℝ) ^ (p - 1) *
        ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ S, ∑ z ∈ S, ‖A u x z‖ ^ p := by
        rw [hcoef, hsum_eq]

/-! ## The `R`-sum identity -/

set_option maxHeartbeats 8000000 in
lemma peg_sum_R_eq (s L D : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) {f : ℤ → ℂ} (hsupp : SupportIn f L) :
    (∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖)
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2 := by
  classical
  set S := symIcc (L + s * D) with hS
  set Qs := Fintype.piFinset (fun _ : Fin s => arithIcc 1 D) with hQs
  have hRre : ∀ x z : ℤ, (∑ v0 ∈ Qs, ∑ v1 ∈ Qs, cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z))
      = (((‖∑ v0 ∈ Qs, ∑ v1 ∈ Qs, cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖ : ℝ) : ℂ)) := by
    intro x z
    rw [hQs]
    exact peg_R_isReal s D hs hD f x z
  have hstep1 : ((∑ x ∈ S, ∑ z ∈ S,
        ‖∑ v0 ∈ Qs, ∑ v1 ∈ Qs, cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖ : ℝ) : ℂ)
      = ∑ x ∈ S, ∑ z ∈ S, (∑ v0 ∈ Qs, ∑ v1 ∈ Qs,
          cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    exact (hRre x z).symm
  have hdbl := peg_double_sum_eq S Qs (fun v0 v1 y => cubeTerm v1 v0 f y)
  have htsum : ∀ v0 v1 : Fin s → ℤ, v0 ∈ Qs →
      (∑ x ∈ S, cubeTerm v1 v0 f x) = ∑' x : ℤ, cubeTerm v1 v0 f x := by
    intro v0 v1 hv0
    rw [hQs] at hv0
    simp only [hS]
    exact (peg_tsum_eq_sum_symIcc (supportIn_cubeTerm (s := s) (L := L) (D := D)
      hsupp (fun i => natAbs_le_of_mem_arithIcc (Fintype.mem_piFinset.mp hv0 i)))).symm
  have hstep2 : (∑ x ∈ S, ∑ z ∈ S, (∑ v0 ∈ Qs, ∑ v1 ∈ Qs,
          cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)))
      = ((∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hdbl]
    congr 1
    rw [show (∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ‖∑ x ∈ S, cubeTerm v1 v0 f x‖ ^ 2)
        = (∑ v0 ∈ Qs, ∑ v1 ∈ Qs, ‖∑' x : ℤ, cubeTerm v1 v0 f x‖ ^ 2) from by
      refine Finset.sum_congr rfl (fun v0 hv0 => Finset.sum_congr rfl (fun v1 _ => ?_))
      rw [htsum v0 v1 hv0]]
    rw [hQs]
    rw [Finset.sum_comm]
  exact Complex.ofReal_injective (hstep1.trans hstep2)


/-! ## Summation bookkeeping -/

lemma peg_const3 {s : ℕ} (Qs : Finset (Fin s → ℤ)) (S : Finset ℤ) (c : ℝ)
    (g : (Fin s → ℤ) → ℤ → ℤ → ℝ) :
    (∑ u ∈ Qs, ∑ x ∈ S, ∑ z ∈ S, c * g u x z)
      = c * ∑ u ∈ Qs, ∑ x ∈ S, ∑ z ∈ S, g u x z := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => (Finset.mul_sum ..).symm)

lemma peg_sum_const3 {s : ℕ} (Qs : Finset (Fin s → ℤ)) (S : Finset ℤ) (c : ℝ)
    (g : ℤ → ℤ → ℝ) :
    (∑ u ∈ Qs, ∑ x ∈ S, ∑ z ∈ S, c * g x z)
      = c * ((Qs.card : ℝ) * ∑ x ∈ S, ∑ z ∈ S, g x z) := by
  have h1 : (∑ x ∈ S, ∑ z ∈ S, c * g x z) = c * ∑ x ∈ S, ∑ z ∈ S, g x z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => (Finset.mul_sum ..).symm)
  calc (∑ u ∈ Qs, ∑ x ∈ S, ∑ z ∈ S, c * g x z)
      = ∑ u ∈ Qs, c * (∑ x ∈ S, ∑ z ∈ S, g x z) := Finset.sum_congr rfl (fun u _ => h1)
    _ = c * ∑ u ∈ Qs, (∑ x ∈ S, ∑ z ∈ S, g x z) := (Finset.mul_sum ..).symm
    _ = c * ((Qs.card : ℝ) * ∑ x ∈ S, ∑ z ∈ S, g x z) := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma peg_symIcc_card_le {L D s : ℕ} (hL : 1 ≤ L) (hDL : D ≤ L) :
    (symIcc (L + s * D)).card ≤ (2 * s + 3) * L := by
  rw [card_symIcc]
  have h1 : s * D ≤ s * L := Nat.mul_le_mul_left s hDL
  calc 2 * (L + s * D) + 1 ≤ 2 * (L + s * L) + L := by omega
    _ = (2 * s + 3) * L := by ring

set_option maxHeartbeats 8000000 in
lemma peg_sum3_le (s D L : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) (f : ℤ → ℂ)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ)
    (hblind : ∀ i u v a b, ψ i u (Function.update v i a) = ψ i u (Function.update v i b))
    (C₁ : ℝ)
    (hC₁ : ∀ (u : Fin s → ℤ) (x z : ℤ),
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x *
                star (cubeTerm u (Concat.mix ω v0 v1) f z))‖
        ≤ C₁ * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
        ‖∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm u v f x * star (cubeTerm u v f z) *
              (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                * ((x : ℝ) - (z : ℝ))))‖ ^ (2 ^ s))
      ≤ (D : ℝ) ^ (s * (2 ^ s - 2)) * C₁ *
        (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
          (∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖)) := by
  classical
  have hper1 : ∀ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∀ x ∈ symIcc (L + s * D), ∀ z ∈ symIcc (L + s * D),
      ‖∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          cubeTerm u v f x * star (cubeTerm u v f z) *
            (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
              * ((x : ℝ) - (z : ℝ))))‖ ^ (2 ^ s)
        ≤ (D : ℝ) ^ (s * (2 ^ s - 2)) *
          ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
                (cubeTerm u (Concat.mix ω v0 v1) f x *
                  star (cubeTerm u (Concat.mix ω v0 v1) f z))‖ :=
    fun u _ x _ z _ => peg_gcsPow s D hs hD f u ψ hblind x z
  have hper2 : ∀ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∀ x ∈ symIcc (L + s * D), ∀ z ∈ symIcc (L + s * D),
      ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x *
                star (cubeTerm u (Concat.mix ω v0 v1) f z))‖
        ≤ C₁ * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖ :=
    fun u _ x _ z _ => hC₁ u x z
  calc (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
          ‖∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ))))‖ ^ (2 ^ s))
      ≤ ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            (D : ℝ) ^ (s * (2 ^ s - 2)) *
              ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                  ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
                    (cubeTerm u (Concat.mix ω v0 v1) f x *
                      star (cubeTerm u (Concat.mix ω v0 v1) f z))‖ :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun x hx =>
          Finset.sum_le_sum (fun z hz => hper1 u hu x hx z hz)))
    _ = (D : ℝ) ^ (s * (2 ^ s - 2)) *
          (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
              ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                  ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
                    (cubeTerm u (Concat.mix ω v0 v1) f x *
                      star (cubeTerm u (Concat.mix ω v0 v1) f z))‖) :=
        peg_const3 _ _ _ _
    _ ≤ (D : ℝ) ^ (s * (2 ^ s - 2)) *
          (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
              C₁ * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                  ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                    cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun x hx =>
            Finset.sum_le_sum (fun z hz => hper2 u hu x hx z hz)))) (by positivity)
    _ = (D : ℝ) ^ (s * (2 ^ s - 2)) *
          (C₁ * (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            (∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
              ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                  cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖))) := by
        rw [peg_sum_const3 _ _ C₁ _]
    _ = (D : ℝ) ^ (s * (2 ^ s - 2)) * C₁ *
        (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
          (∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖)) := by ring


/-! ## The final arithmetic -/

set_option maxHeartbeats 8000000 in
lemma peg_final_arith (s : ℕ) (hs : 1 ≤ s) (D L Q Sc C₁ Ec Eu γ : ℝ)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hC₁ : 0 < C₁) (hγ : 0 < γ)
    (hQ : Q = D ^ s) (hSc0 : 0 ≤ Sc) (hSc : Sc ≤ (2 * (s : ℝ) + 3) * L)
    (hEu : 0 ≤ Eu)
    (hhyp : γ ≤ Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Ec))
    (hmid : Ec ^ (2 ^ s) ≤ (Q * Sc ^ 2) ^ (2 ^ s - 1) * (D ^ (s * (2 ^ s - 2)) * C₁ * (Q * Eu))) :
    γ ^ (2 ^ s) ≤
      (C₁ * (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2)) * (Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Eu)) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hLne : L ≠ 0 := ne_of_gt hL0
  have h2pow : 2 ≤ 2 ^ s := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnonneg : 0 ≤ (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) := by
    have h1 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (le_of_lt hQpos)
    have h2 : 0 ≤ L⁻¹ := inv_nonneg.mpr (le_of_lt hL0)
    positivity
  -- the `D`/`Q` cancellation
  have hQcancel : (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * Q ^ (2 ^ s - 1) * Q *
      D ^ (s * (2 ^ s - 2)) = Q⁻¹ * Q⁻¹ := by
    have hDpow : D ^ (s * (2 ^ s - 2)) = Q ^ (2 ^ s - 2) := by
      rw [hQ, ← pow_mul]
    rw [hDpow]
    have e1 : (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) = (Q ^ (2 ^ s + 2 ^ s))⁻¹ := by
      rw [← pow_add, inv_pow]
    rw [e1]
    have e2 : Q ^ (2 ^ s - 1) * Q * Q ^ (2 ^ s - 2) = Q ^ (2 ^ s + 2 ^ s - 2) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    have hregroup : (Q ^ (2 ^ s + 2 ^ s))⁻¹ * Q ^ (2 ^ s - 1) * Q * Q ^ (2 ^ s - 2)
        = (Q ^ (2 ^ s + 2 ^ s))⁻¹ * (Q ^ (2 ^ s - 1) * Q * Q ^ (2 ^ s - 2)) := by
      ring
    rw [hregroup, e2]
    have e3 : Q ^ (2 ^ s + 2 ^ s - 2) = Q ^ (2 ^ s + 2 ^ s) * (Q ^ 2)⁻¹ := by
      have h := pow_sub₀ Q hQne (m := 2 ^ s + 2 ^ s) (n := 2) (by omega)
      simpa using h
    rw [e3, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hQne), one_mul, pow_two, mul_inv]
  -- the `L` cancellation
  have hLc : ((L⁻¹) ^ 2) ^ (2 ^ s) * L ^ (2 * (2 ^ s - 1)) = (L⁻¹) ^ 2 := by
    rw [← pow_mul]
    simp only [inv_pow]
    have e2 : L ^ (2 * (2 ^ s - 1)) = L ^ (2 * 2 ^ s - 2) := by
      congr 1
      omega
    rw [e2]
    have e3 : L ^ (2 * 2 ^ s - 2) = L ^ (2 * 2 ^ s) * (L ^ 2)⁻¹ := by
      have h := pow_sub₀ L hLne (m := 2 * 2 ^ s) (n := 2) (by omega)
      simpa using h
    rw [e3, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hLne), one_mul, pow_two, mul_inv]
  -- the `L`/`Sc` bound
  have hLbound : ((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))
      ≤ (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2) * (L⁻¹) ^ 2 := by
    have hstep : Sc ^ (2 * (2 ^ s - 1)) ≤ ((2 * (s : ℝ) + 3) * L) ^ (2 * (2 ^ s - 1)) :=
      pow_le_pow_left₀ hSc0 hSc _
    calc ((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))
        ≤ ((L⁻¹) ^ 2) ^ (2 ^ s) * ((2 * (s : ℝ) + 3) * L) ^ (2 * (2 ^ s - 1)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = ((2 * (s : ℝ) + 3)) ^ (2 * (2 ^ s - 1)) *
            (((L⁻¹) ^ 2) ^ (2 ^ s) * L ^ (2 * (2 ^ s - 1))) := by
          rw [mul_pow]; ring
      _ = ((2 * (s : ℝ) + 3)) ^ (2 * (2 ^ s - 1)) * (L⁻¹) ^ 2 := by rw [hLc]
      _ = (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2) * (L⁻¹) ^ 2 := by
          congr 1
          congr 1
          omega
  -- combine
  have hpow1 : (Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Ec)) ^ (2 ^ s)
      = (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) * Ec ^ (2 ^ s) := by
    rw [mul_pow, mul_pow, mul_pow]
    ring
  have hstep2 : (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) * Ec ^ (2 ^ s)
      ≤ (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) *
          ((Q * Sc ^ 2) ^ (2 ^ s - 1) * (D ^ (s * (2 ^ s - 2)) * C₁ * (Q * Eu))) :=
    mul_le_mul_of_nonneg_left hmid hnonneg
  have hstep3 : (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) *
        ((Q * Sc ^ 2) ^ (2 ^ s - 1) * (D ^ (s * (2 ^ s - 2)) * C₁ * (Q * Eu)))
      = C₁ * ((Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * Q ^ (2 ^ s - 1) * Q *
            D ^ (s * (2 ^ s - 2))) *
        (((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))) * Eu := by
    rw [mul_pow Q (Sc ^ 2) (2 ^ s - 1)]
    have hSc : (Sc ^ 2) ^ (2 ^ s - 1) = Sc ^ (2 * (2 ^ s - 1)) := by
      rw [← pow_mul]
    rw [hSc]
    ring
  have hstep4 : C₁ * (Q⁻¹ * Q⁻¹) * (((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))) * Eu
      ≤ C₁ * (Q⁻¹ * Q⁻¹) * ((2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2) * (L⁻¹) ^ 2) * Eu := by
    have hc : 0 ≤ C₁ * (Q⁻¹ * Q⁻¹) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLbound hc) hEu
  have hlast : C₁ * (Q⁻¹ * Q⁻¹) * ((2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2) * (L⁻¹) ^ 2) * Eu
      = (C₁ * (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2)) * (Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Eu)) := by
    ring
  calc γ ^ (2 ^ s)
      ≤ (Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Ec)) ^ (2 ^ s) :=
        pow_le_pow_left₀ (le_of_lt hγ) hhyp (2 ^ s)
    _ = (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) * Ec ^ (2 ^ s) := hpow1
    _ ≤ (Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * ((L⁻¹) ^ 2) ^ (2 ^ s) *
          ((Q * Sc ^ 2) ^ (2 ^ s - 1) * (D ^ (s * (2 ^ s - 2)) * C₁ * (Q * Eu))) := hstep2
    _ = C₁ * ((Q⁻¹) ^ (2 ^ s) * (Q⁻¹) ^ (2 ^ s) * Q ^ (2 ^ s - 1) * Q *
            D ^ (s * (2 ^ s - 2))) *
        (((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))) * Eu := hstep3
    _ = C₁ * (Q⁻¹ * Q⁻¹) * (((L⁻¹) ^ 2) ^ (2 ^ s) * Sc ^ (2 * (2 ^ s - 1))) * Eu := by
        rw [hQcancel]
    _ ≤ C₁ * (Q⁻¹ * Q⁻¹) * ((2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2) * (L⁻¹) ^ 2) * Eu := hstep4
    _ = (C₁ * (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2)) * (Q⁻¹ * Q⁻¹ * ((L⁻¹) ^ 2 * Eu)) := hlast


/-! ## The assembly -/

lemma peg_sum_comm4' {α β γ δ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (F : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d)
      = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, F a b c d := by
  have h1 : ∀ a : α, (∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d)
      = ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, F a b c d := by
    intro a
    have h := peg_sum_comm4 ({a} : Finset α) t u v (fun _ b c d => F a b c d)
    simpa using h
  exact Finset.sum_congr rfl (fun a _ => h1 a)

lemma peg_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

set_option maxHeartbeats 8000000 in
lemma peg_middle (s D L : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) {f : ℤ → ℂ} (hsupp : SupportIn f L)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ)
    (hblind : ∀ i u v a b, ψ i u (Function.update v i a) = ψ i u (Function.update v i b))
    (C₁ : ℝ)
    (hC₁ : ∀ (u : Fin s → ℤ) (x z : ℤ),
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (cubeTerm u (Concat.mix ω v0 v1) f x *
                star (cubeTerm u (Concat.mix ω v0 v1) f z))‖
        ≤ C₁ * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖) :
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2) ^ (2 ^ s)
      ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            ((symIcc (L + s * D)).card : ℝ) ^ 2) ^ (2 ^ s - 1) *
        ((D : ℝ) ^ (s * (2 ^ s - 2)) * C₁ *
          (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2))) := by
  classical
  have hEc_nonneg : 0 ≤ ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ‖∑' x : ℤ, cubeTerm u v f x *
          Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hchirp := peg_chirped_expand s L D hD hsupp ψ
  have hreord := peg_sum_comm4' (Fintype.piFinset (fun _ : Fin s => arithIcc 1 D))
    (Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)) (symIcc (L + s * D)) (symIcc (L + s * D))
    (fun u v x z => cubeTerm u v f x * star (cubeTerm u v f z) *
      (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v) * ((x : ℝ) - (z : ℝ)))))
  have hA : (((∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2) : ℝ) : ℂ)
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            (∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ))))) := hchirp.trans hreord
  have hEc0 : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2)
      = ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            (∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ)))))‖ := by
    have hnorm : ‖(((∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2) : ℝ) : ℂ)‖
        = (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2) := by
      rw [peg_norm_ofReal, abs_of_nonneg hEc_nonneg]
    rw [← hnorm]
    exact congrArg norm hA
  have hHolder := peg_sum_pow_le_card s D hD (symIcc (L + s * D))
    (fun u x z => ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      cubeTerm u v f x * star (cubeTerm u v f z) *
        (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
          * ((x : ℝ) - (z : ℝ))))) (2 ^ s) (Nat.one_le_two_pow)
  have h3 := peg_sum3_le s D L hs hD f ψ hblind C₁ hC₁
  rw [hEc0]
  have hHolder' := hHolder
  rw [show (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card *
        (symIcc (L + s * D)).card ^ 2 : ℕ) : ℝ)
      = ((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
        ((symIcc (L + s * D)).card : ℝ) ^ 2 by push_cast; ring] at hHolder'
  calc ‖∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            (∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ)))))‖ ^ (2 ^ s)
      ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            ((symIcc (L + s * D)).card : ℝ) ^ 2) ^ (2 ^ s - 1) *
        (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
            ‖∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              cubeTerm u v f x * star (cubeTerm u v f z) *
                (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * (ψ i u v)
                  * ((x : ℝ) - (z : ℝ))))‖ ^ (2 ^ s)) := hHolder'
    _ ≤ (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            ((symIcc (L + s * D)).card : ℝ) ^ 2) ^ (2 ^ s - 1) *
        ((D : ℝ) ^ (s * (2 ^ s - 2)) * C₁ *
          (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            (∑ x ∈ symIcc (L + s * D), ∑ z ∈ symIcc (L + s * D),
              ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                  cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            ((symIcc (L + s * D)).card : ℝ) ^ 2) ^ (2 ^ s - 1) *
        ((D : ℝ) ^ (s * (2 ^ s - 2)) * C₁ *
          (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℝ) *
            (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
                ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2))) := by
        rw [peg_sum_R_eq s L D hs hD hsupp]


set_option maxHeartbeats 8000000 in
theorem phaseElimGap_of_flatCube (s : ℕ) (hs : 1 ≤ s)
    (hflat : ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (h : Fin s → ℤ) (g : ℤ → ℂ),
        1 ≤ D → (∀ t : ℤ, ‖g t‖ ≤ 1) →
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (Work.Peluse.cubeTerm h (Work.Peluse.Concat.mix ω v0 v1) g 0)‖
        ≤ C * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (g (Work.Peluse.cornerShift v1 v0 ω))‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L D : ℕ) (f : ℤ → ℂ) (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ),
        1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f L →
        (∀ i : Fin s, ∀ u : Fin s → ℤ, ∀ v : Fin s → ℤ, ∀ a b : ℤ,
          ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) →
        ∀ γ : ℝ, 0 < γ →
        γ ≤ ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x *
                  Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 →
        γ ^ (2 ^ s) ≤ C *
          (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hflat
  obtain ⟨C₁, hC₁pos, hC₁⟩ := peg_hflat_apply s hs ⟨C₀, hC₀pos, hC₀⟩
  refine ⟨C₁ * (2 * (s : ℝ) + 3) ^ (2 * 2 ^ s - 2), by positivity, ?_⟩
  intro L D f ψ hL hD hDL hf hsupp hblind γ hγ hhyp
  simp only [← arithIcc_one_eq D] at hhyp ⊢
  have hnormL : ∀ r : ℂ, ‖((L : ℂ))⁻¹ * r‖ ^ 2 = ((L : ℝ)⁻¹) ^ 2 * ‖r‖ ^ 2 := by
    intro r
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    ring
  have hc : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖((L : ℂ))⁻¹ * ∑' x : ℤ, cubeTerm u v f x *
            Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2)
      = ((L : ℝ)⁻¹) ^ 2 *
        (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ‖∑' x : ℤ, cubeTerm u v f x *
              Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => hnormL _)
  have hu : (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ‖((L : ℂ))⁻¹ * ∑' x : ℤ, cubeTerm u v f x‖ ^ 2)
      = ((L : ℝ)⁻¹) ^ 2 *
        (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => hnormL _)
  have hC₁' : ∀ (u : Fin s → ℤ) (x z : ℤ),
      ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            (cubeTerm u (Concat.mix ω v0 v1) f x *
              star (cubeTerm u (Concat.mix ω v0 v1) f z))‖
      ≤ C₁ * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
            cubeTerm v1 v0 f x * star (cubeTerm v1 v0 f z)‖ :=
    fun u x z => hC₁ D f u x z hD hf
  have hmid := peg_middle s D L hs hD hsupp ψ hblind C₁ hC₁'
  have hcardQ : (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℕ) : ℝ)
      = (D : ℝ) ^ s := by
    rw [card_piFinset_arithIcc]
    push_cast
    ring
  have hScard : (((symIcc (L + s * D)).card : ℕ) : ℝ) ≤ (2 * (s : ℝ) + 3) * L := by
    have h := peg_symIcc_card_le (L := L) (D := D) (s := s) hL (by exact_mod_cast hDL)
    have h2 : (((symIcc (L + s * D)).card : ℕ) : ℝ) ≤ (((2 * s + 3) * L : ℕ) : ℝ) := by
      exact_mod_cast h
    calc (((symIcc (L + s * D)).card : ℕ) : ℝ) ≤ (((2 * s + 3) * L : ℕ) : ℝ) := h2
      _ = (2 * (s : ℝ) + 3) * L := by push_cast; ring
  have hEu : 0 ≤ (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2) :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  rw [hc] at hhyp
  rw [hu]
  exact peg_final_arith s hs (D : ℝ) (L : ℝ)
    (((Fintype.piFinset (fun _ : Fin s => arithIcc 1 D)).card : ℕ) : ℝ)
    (((symIcc (L + s * D)).card : ℕ) : ℝ) C₁
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ‖∑' x : ℤ, cubeTerm u v f x *
          Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2)
    (∑ u ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin s => arithIcc 1 D),
        ‖∑' x : ℤ, cubeTerm u v f x‖ ^ 2) γ
    (by exact_mod_cast hD) (by exact_mod_cast hL) hC₁pos hγ hcardQ
    (by positivity) hScard hEu hhyp hmid

end

end Work.Peluse.Ulower
