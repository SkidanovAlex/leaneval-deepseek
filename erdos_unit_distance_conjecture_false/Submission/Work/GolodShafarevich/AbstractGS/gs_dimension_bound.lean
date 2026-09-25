import Mathlib
import Submission.Work.GolodShafarevich.AbstractGS.gs_series_aux

namespace Work.GolodShafarevich.AbstractGS

open scoped BigOperators

noncomputable section

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]

/-- `I ^ n` viewed as a `k`-submodule of `B`. -/
def Isub (k : Type*) [Field k] {B : Type*} [Ring B] [Algebra k B] (I : Ideal B) (n : ℕ) :
    Submodule k B := Submodule.restrictScalars k (I ^ n : Ideal B)

/-- `dim_k (B / I^n)`. -/
def qdim (k : Type*) [Field k] {B : Type*} [Ring B] [Algebra k B] (I : Ideal B) (n : ℕ) : ℕ :=
  Module.finrank k (B ⧸ Isub k I n)

/-- `dim_k (I^n)`. -/
def idim (k : Type*) [Field k] {B : Type*} [Ring B] [Algebra k B] (I : Ideal B) (n : ℕ) : ℕ :=
  Module.finrank k (Isub k I n)

/-- The `B`-submodule `(I^m)^d` of `B^d = Fin d → B`. -/
def Tsub (I : Ideal B) (d : ℕ) (m : ℕ) : Submodule B (Fin d → B) :=
  Submodule.pi Set.univ (fun _ : Fin d => (I ^ m : Ideal B))

/-- The `B`-submodule `ker ψ ∩ (I^m)^d`. -/
def Fsub {d : ℕ} (ψ : (Fin d → B) →ₗ[B] B) (I : Ideal B) (m : ℕ) :
    Submodule B (Fin d → B) := LinearMap.ker ψ ⊓ Tsub I d m

lemma Isub_zero (I : Ideal B) : Isub k I 0 = ⊤ := by
  rw [Isub, Submodule.pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top]

lemma Isub_one (I : Ideal B) : Isub k I 1 = Submodule.restrictScalars k I := by
  rw [Isub, Submodule.pow_one]

lemma Isub_mono (I : Ideal B) {m n : ℕ} (h : m ≤ n) : Isub k I n ≤ Isub k I m := by
  rw [Isub, Isub, Submodule.restrictScalars_le]
  exact Ideal.pow_le_pow_right h

lemma qdim_add_idim (I : Ideal B) (n : ℕ) [FiniteDimensional k B] :
    qdim k I n + idim k I n = Module.finrank k B :=
  Submodule.finrank_quotient_add_finrank (Isub k I n)

lemma qdim_mono (I : Ideal B) {m n : ℕ} (h : m ≤ n) [FiniteDimensional k B] :
    qdim k I m ≤ qdim k I n := by
  have h1 := qdim_add_idim (k := k) I m
  have h2 := qdim_add_idim (k := k) I n
  have h3 : idim k I n ≤ idim k I m := Submodule.finrank_mono (Isub_mono (k := k) I h)
  omega

/-- An antitone sequence of naturals is eventually constant. -/
lemma antitone_eventually_const (d : ℕ → ℕ) (h : Antitone d) : ∃ N, ∀ n ≥ N, d n = d N := by
  have hne : (Set.range d).Nonempty := ⟨d 0, 0, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, d N = sInf (Set.range d) := by
    obtain ⟨m, hm⟩ := Nat.sInf_mem hne
    exact ⟨m, hm⟩
  refine ⟨N, fun n hn => le_antisymm (h hn) ?_⟩
  rw [hN]
  exact Nat.sInf_le ⟨n, rfl⟩

/-- A monotone sequence of naturals bounded above is eventually constant. -/
lemma monotone_eventually_const (c : ℕ → ℕ) (hmono : Monotone c) (M : ℕ) (hM : ∀ n, c n ≤ M) :
    ∃ N, ∀ n ≥ N, c n = c N := by
  have hd : Antitone (fun n => M - c n) := fun a b hab => Nat.sub_le_sub_left (hmono hab) M
  obtain ⟨N, hN⟩ := antitone_eventually_const _ hd
  refine ⟨N, fun n hn => ?_⟩
  have h1 : M - c n = M - c N := hN n hn
  have h2 : c n ≤ M := hM n
  have h3 : c N ≤ M := hM N
  omega

lemma qdim_eventually_const (I : Ideal B) [FiniteDimensional k B] :
    ∃ N, ∀ n ≥ N, qdim k I n = qdim k I N :=
  monotone_eventually_const (qdim k I) (fun _ _ h => qdim_mono I h) (Module.finrank k B)
    (fun n => by have := qdim_add_idim (k := k) I n; omega)

/-- Right-closure of `I^n`, derived from `finrank_k (B/I) = 1`. -/
lemma pow_right_closed [FiniteDimensional k B] {I : Ideal B}
    (hI : Module.finrank k (B ⧸ I) = 1) :
    ∀ (m : ℕ) (a : B), a ∈ I ^ m → ∀ b : B, a * b ∈ I ^ m := by
  have hIright : ∀ a ∈ I, ∀ b : B, a * b ∈ I := by
    have h1ne : (Submodule.Quotient.mk (1 : B) : B ⧸ I) ≠ 0 := by
      intro h
      rw [Submodule.Quotient.mk_eq_zero] at h
      have htop : I = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro x
        rw [← mul_one x]
        exact Submodule.smul_mem I x h
      have hsub : Subsingleton (B ⧸ I) := by rw [htop]; infer_instance
      have h0 : Module.finrank k (B ⧸ I) = 0 := Module.finrank_zero_of_subsingleton
      omega
    have hspan : Submodule.span k {(Submodule.Quotient.mk (1 : B) : B ⧸ I)} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton h1ne, hI]
    intro a ha b
    have hb : (Submodule.Quotient.mk b : B ⧸ I) ∈
        Submodule.span k {(Submodule.Quotient.mk (1 : B) : B ⧸ I)} := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hb
    obtain ⟨c, hc⟩ := hb
    rw [← Submodule.Quotient.mk_eq_zero]
    calc (Submodule.Quotient.mk (a * b) : B ⧸ I)
        = a • (Submodule.Quotient.mk b : B ⧸ I) := by
          rw [show a * b = a • b from rfl, Submodule.Quotient.mk_smul]
      _ = a • (c • (Submodule.Quotient.mk (1 : B) : B ⧸ I)) := by rw [hc]
      _ = c • (a • (Submodule.Quotient.mk (1 : B) : B ⧸ I)) := by rw [smul_comm]
      _ = c • (Submodule.Quotient.mk a : B ⧸ I) := by
          congr 1
          rw [← Submodule.Quotient.mk_smul I a (1 : B)]
          congr 1
          rw [smul_eq_mul, mul_one]
      _ = 0 := by rw [(Submodule.Quotient.mk_eq_zero I).mpr ha, smul_zero]
  intro m
  induction m with
  | zero =>
    intro a ha b
    rw [Submodule.pow_zero, Ideal.one_eq_top] at ha ⊢
    exact Submodule.mem_top
  | succ m ih =>
    intro a ha b
    have hkey : I ^ m * I ≤ Submodule.comap (LinearMap.mulRight B b) (I ^ (m+1)) := by
      refine Submodule.mul_le.mpr ?_
      intro c hc e he
      show c * e * b ∈ I ^ (m+1)
      rw [mul_assoc]
      exact Submodule.mul_mem_mul hc (hIright e he b)
    rw [Submodule.pow_succ] at ha
    exact hkey ha

/-- `finrank_k (I^m)^ι = #ι * finrank_k (I^m)`. -/
lemma finrank_Tsub {I : Ideal B} (m : ℕ) (ι : Type*) [Fintype ι] [FiniteDimensional k B] :
    Module.finrank k ↥(Submodule.pi Set.univ (fun _ : ι => (I ^ m : Ideal B))) =
      Fintype.card ι * idim k I m := by
  have e : ↥(Submodule.pi Set.univ (fun _ : ι => (I ^ m : Ideal B))) ≃ₗ[k]
      (ι → ↥(Isub k I m)) :=
  { toFun := fun y i => ⟨y.1 i, Submodule.restrictScalars_mem k (I ^ m) (y.1 i) |>.mpr
      (Submodule.mem_pi.mp y.2 i (Set.mem_univ i))⟩
    invFun := fun z => ⟨fun i => (z i).1, Submodule.mem_pi.mpr (fun i _ =>
      Submodule.restrictScalars_mem k (I ^ m) ((z i).1) |>.mp (z i).2)⟩
    left_inv := fun y => rfl
    right_inv := fun z => rfl
    map_add' := fun y z => rfl
    map_smul' := fun c y => rfl }
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

/-- The range of `ψ` restricted to `(I^m)^d` is `I^(m+1)`. -/
lemma map_Tsub_eq [FiniteDimensional k B] {I : Ideal B} {d : ℕ} (ψ : (Fin d → B) →ₗ[B] B)
    (hψ : LinearMap.range ψ = I) (hI : Module.finrank k (B ⧸ I) = 1) (m : ℕ) :
    Submodule.map ψ (Tsub I d m) = (I ^ (m + 1) : Ideal B) := by
  have hInright := pow_right_closed (k := k) hI
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap]
    have hy' : y ∈ Submodule.pi Set.univ (fun _ : Fin d => (I ^ m : Ideal B)) := hy
    have hydecomp : y = ∑ i, y i • (Pi.single i (1 : B)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hydecomp, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    refine Submodule.mul_mem_mul (Submodule.mem_pi.mp hy' i (Set.mem_univ i)) ?_
    have h2 : ψ (Pi.single i (1 : B)) ∈ LinearMap.range ψ := ⟨Pi.single i 1, rfl⟩
    rwa [hψ] at h2
  · rw [Submodule.pow_succ]
    refine Submodule.mul_le.mpr ?_
    intro a ha b hb
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (hψ ▸ hb : b ∈ LinearMap.range ψ)
    refine Submodule.mem_map.mpr ⟨fun i => a * w i, ?_, ?_⟩
    · show (fun i => a * w i) ∈ Tsub I d m
      intro i _
      exact hInright m a ha (w i)
    · show ψ (fun i => a * w i) = a * b
      have h1 : (fun i => a * w i) = a • w := by funext i; rw [Pi.smul_apply, smul_eq_mul]
      rw [h1, map_smul, smul_eq_mul, hw]

/-- `Fsub` in degree `0` is `ker ψ`. -/
lemma Fsub_zero {d : ℕ} (ψ : (Fin d → B) →ₗ[B] B) (I : Ideal B) :
    Fsub ψ I 0 = LinearMap.ker ψ := by
  rw [Fsub, Tsub]
  have : Submodule.pi Set.univ (fun _ : Fin d => (I ^ 0 : Ideal B)) = ⊤ := by
    simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.pi_top]
  rw [this, inf_top_eq]

/-- `Fsub m ⊆ Fsub m'` for `m ≥ m'`. -/
lemma Fsub_anti {d : ℕ} (ψ : (Fin d → B) →ₗ[B] B) (I : Ideal B) {m m' : ℕ} (h : m' ≤ m) :
    Fsub ψ I m ≤ Fsub ψ I m' := by
  rw [Fsub, Fsub]
  exact inf_le_inf_left _ (Submodule.pi_mono (fun _ _ => Ideal.pow_le_pow_right h))

/-- Rank–nullity for the restriction of `ψ` to `(I^m)^d`. -/
lemma rank_nullity_Fsub [FiniteDimensional k B] {I : Ideal B} {d : ℕ} (ψ : (Fin d → B) →ₗ[B] B)
    (hψ : LinearMap.range ψ = I) (hI : Module.finrank k (B ⧸ I) = 1) (m : ℕ) :
    idim k I (m + 1) + Module.finrank k ↥(Fsub ψ I m) = d * idim k I m := by
  have hmap := map_Tsub_eq (k := k) ψ hψ hI m
  let Ψ : ↥(Submodule.restrictScalars k (Tsub I d m)) →ₗ[k] B :=
    (LinearMap.restrictScalars k ψ).comp (Submodule.subtype (Submodule.restrictScalars k (Tsub I d m)))
  have hrange : Ψ.range = Isub k I (m + 1) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    change Submodule.map (LinearMap.restrictScalars k ψ)
        (Submodule.restrictScalars k (Tsub I d m)) = Submodule.restrictScalars k (I ^ (m + 1) : Ideal B)
    rw [show Submodule.map (LinearMap.restrictScalars k ψ)
          (Submodule.restrictScalars k (Tsub I d m))
        = Submodule.restrictScalars k (Submodule.map ψ (Tsub I d m)) from rfl, hmap]
  have hker : Module.finrank k ↥(Ψ.ker) = Module.finrank k ↥(Fsub ψ I m) := by
    have e : ↥(Ψ.ker) ≃ₗ[k] ↥(Submodule.restrictScalars k (Fsub ψ I m)) :=
    { toFun := fun y => ⟨y.1.1, (Submodule.restrictScalars_mem k (Fsub ψ I m) y.1.1).mpr
        ⟨y.2, (Submodule.restrictScalars_mem k (Tsub I d m) y.1.1).mp y.1.2⟩⟩
      invFun := fun z => ⟨⟨z.1, (Submodule.restrictScalars_mem k (Tsub I d m) z.1).mpr
        ((Submodule.mem_inf.mp ((Submodule.restrictScalars_mem k (Fsub ψ I m) z.1).mp z.2)).2)⟩,
        (Submodule.mem_inf.mp ((Submodule.restrictScalars_mem k (Fsub ψ I m) z.1).mp z.2)).1⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl
      map_add' := fun y z => rfl
      map_smul' := fun c y => rfl }
    rw [LinearEquiv.finrank_eq e]
    rfl
  have hdom : Module.finrank k ↥(Submodule.restrictScalars k (Tsub I d m)) = d * idim k I m := by
    rw [show Module.finrank k ↥(Submodule.restrictScalars k (Tsub I d m))
        = Module.finrank k ↥(Submodule.pi Set.univ (fun _ : Fin d => (I ^ m : Ideal B))) from rfl]
    rw [finrank_Tsub (k := k) (I := I) m (Fin d)]
    rw [Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hrange, hker, hdom] at hrn
  rw [idim]
  exact hrn

/-- The dimension bound coming from the `r` generators of `ker ψ`. -/
lemma rank_bound_Fsub [FiniteDimensional k B] {I : Ideal B} {d r : ℕ} (ψ : (Fin d → B) →ₗ[B] B)
    (v : Fin r → (Fin d → B))
    (hspan : Submodule.span B (Set.range v) = LinearMap.ker ψ)
    (hvI : ∀ (j : Fin r) (i : Fin d), v j i ∈ I) {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank k ↥(Fsub ψ I 0) - Module.finrank k ↥(Fsub ψ I n) ≤ r * qdim k I (n - 1) := by
  let W : (Fin r → B) →ₗ[B] (Fin d → B) :=
  { toFun := fun y i => ∑ j, y j * v j i
    map_add' := by
      intro x y; funext i
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c y; funext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply, mul_assoc] }
  have hWspan : Submodule.span B (Set.range v) = Submodule.map W ⊤ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨j, rfl⟩
      refine Submodule.mem_map.mpr ⟨(Pi.single j (1 : B) : Fin r → B), Submodule.mem_top, ?_⟩
      funext i
      show (∑ k, (Pi.single j (1 : B) : Fin r → B) k * v k i) = v j i
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul]
      · intro k _ hk; rw [Pi.single_eq_of_ne hk, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    · rw [Submodule.map_le_iff_le_comap]
      intro y _
      rw [Submodule.mem_comap]
      have hy : W y = ∑ j, y j • v j := by
        funext i
        rw [show (W y) i = ∑ j, y j * v j i from rfl, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]
      rw [hy]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem (Submodule.span B (Set.range v)) (y j)
          (Submodule.subset_span (Set.mem_range_self j))
  have hWrange : W.range = LinearMap.ker ψ := by
    rw [LinearMap.range_eq_map, ← hWspan, hspan]
  have hmem : ∀ y, W y ∈ Fsub ψ I 0 := by
    intro y
    rw [Fsub_zero]
    exact hWrange ▸ LinearMap.mem_range.mpr ⟨y, rfl⟩
  -- everything from here on is `k`-flavoured
  let Xk : Submodule k (Fin d → B) := Submodule.restrictScalars k (Fsub ψ I 0)
  let Nk : Submodule k ↥Xk :=
    Submodule.comap Xk.subtype (Submodule.restrictScalars k (Fsub ψ I n))
  let Dk : Submodule k (Fin r → B) := Submodule.restrictScalars k (Tsub I r (n - 1))
  have hmemk : ∀ y, W y ∈ Xk :=
    fun y => (Submodule.restrictScalars_mem k (Fsub ψ I 0) (W y)).mpr (hmem y)
  let g : (Fin r → B) →ₗ[k] ↥Xk := (LinearMap.restrictScalars k W).codRestrict Xk hmemk
  let Φ : (Fin r → B) →ₗ[k] (↥Xk ⧸ Nk) := (Submodule.mkQ Nk).comp g
  have hkerΦ : Dk ≤ Φ.ker := by
    intro y hy
    rw [LinearMap.mem_ker]
    show (Submodule.mkQ Nk) (g y) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change W y ∈ Submodule.restrictScalars k (Fsub ψ I n)
    rw [Submodule.restrictScalars_mem, Fsub, Submodule.mem_inf]
    refine ⟨hWrange ▸ LinearMap.mem_range.mpr ⟨y, rfl⟩, ?_⟩
    intro i _
    have hy' : y ∈ Tsub I r (n - 1) := by
      rw [← Submodule.restrictScalars_mem k (Tsub I r (n - 1))]; exact hy
    show (∑ j, y j * v j i) ∈ I ^ n
    rw [show I ^ n = I ^ (n - 1) * I from by
      rw [← Submodule.pow_succ, Nat.sub_add_cancel hn]]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.mul_mem_mul (Submodule.mem_pi.mp hy' j (Set.mem_univ j)) (hvI j i)
  have hsurj : Φ.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      have hz : z.1 ∈ LinearMap.range W := by
        have h : z.1 ∈ LinearMap.ker ψ := by
          rw [← Fsub_zero ψ I]
          exact ((Submodule.restrictScalars_mem k (Fsub ψ I 0) z.1).mp z.2)
        rwa [hWrange]
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hz
      exact ⟨y, by
        show (Submodule.mkQ Nk) (g y) = Submodule.Quotient.mk z
        rw [show g y = z from Subtype.ext hy, Submodule.mkQ_apply]⟩
  let Φ' := Submodule.liftQ Dk Φ hkerΦ
  have hrange' : Φ'.range = ⊤ := by
    rw [Submodule.range_liftQ]
    exact hsurj
  have hle : Module.finrank k (↥Xk ⧸ Nk) ≤ Module.finrank k ((Fin r → B) ⧸ Dk) := by
    have h := LinearMap.finrank_range_le Φ'
    rw [hrange', finrank_top] at h
    exact h
  have hQ : Module.finrank k (↥Xk ⧸ Nk)
      = Module.finrank k ↥Xk - Module.finrank k ↥Nk := by
    have h := Submodule.finrank_quotient_add_finrank Nk
    omega
  have hNdim : Module.finrank k ↥Nk = Module.finrank k ↥(Submodule.restrictScalars k (Fsub ψ I n)) := by
    have hle' : Submodule.restrictScalars k (Fsub ψ I n) ≤ Xk := by
      intro z hz
      rw [Submodule.restrictScalars_mem] at hz ⊢
      exact Fsub_anti ψ I (Nat.zero_le n) hz
    have e : ↥Nk ≃ₗ[k] ↥(Submodule.restrictScalars k (Fsub ψ I n)) :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun w => ⟨⟨w.1, hle' w.2⟩, w.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl
      map_add' := fun x y => rfl
      map_smul' := fun c y => rfl }
    rw [LinearEquiv.finrank_eq e]
  have hdomdim : Module.finrank k ((Fin r → B) ⧸ Dk) = r * qdim k I (n - 1) := by
    have h1 := Submodule.finrank_quotient_add_finrank Dk
    have h2 : Module.finrank k ↥Dk = r * idim k I (n - 1) := by
      rw [show Module.finrank k ↥Dk
          = Module.finrank k ↥(Submodule.pi Set.univ (fun _ : Fin r => (I ^ (n-1) : Ideal B)))
          from rfl]
      rw [finrank_Tsub (k := k) (I := I) (n - 1) (Fin r), Fintype.card_fin]
    have h3 : Module.finrank k (Fin r → B) = r * Module.finrank k B := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
    have h4 := qdim_add_idim (k := k) I (n - 1)
    rw [h2, h3] at h1
    have hq : qdim k I (n - 1) = Module.finrank k B - idim k I (n - 1) := by omega
    rw [hq, Nat.mul_sub_left_distrib]
    omega
  have hX : Module.finrank k ↥Xk = Module.finrank k ↥(Fsub ψ I 0) := rfl
  have hXn : Module.finrank k ↥(Submodule.restrictScalars k (Fsub ψ I n))
      = Module.finrank k ↥(Fsub ψ I n) := rfl
  calc Module.finrank k ↥(Fsub ψ I 0) - Module.finrank k ↥(Fsub ψ I n)
      = Module.finrank k ↥Xk - Module.finrank k ↥Nk := by rw [hX, hNdim, hXn]
    _ = Module.finrank k (↥Xk ⧸ Nk) := hQ.symm
    _ ≤ Module.finrank k ((Fin r → B) ⧸ Dk) := hle
    _ = r * qdim k I (n - 1) := hdomdim
/-- The abstract Golod–Shafarevich dimension bound. -/
theorem gs_dimension_bound {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]
    [FiniteDimensional k B] {I : Ideal B} (hI : Module.finrank k (B ⧸ I) = 1)
    {d r : ℕ} (hd : 1 ≤ d) (ψ : (Fin d → B) →ₗ[B] B) (hψ : LinearMap.range ψ = I)
    (v : Fin r → (Fin d → B)) (hspan : Submodule.span B (Set.range v) = LinearMap.ker ψ)
    (hvI : ∀ (j : Fin r) (i : Fin d), v j i ∈ I) :
    4 * r > d ^ 2 := by
  have ha0 : qdim k I 0 = 0 := by
    rw [qdim, Isub_zero]
    exact Module.finrank_zero_of_subsingleton
  have ha1 : qdim k I 1 = 1 := by
    rw [qdim, Isub_one]
    exact hI
  have hmono : Monotone (fun n => qdim k I n) := fun _ _ h => qdim_mono I h
  have hstab : ∃ N, ∀ n ≥ N, qdim k I n = qdim k I N := qdim_eventually_const I
  have hineq : ∀ n : ℕ, 1 ≤ n →
      d * qdim k I n + 1 ≤ qdim k I (n + 1) + r * qdim k I (n - 1) := by
    intro n hn
    have hrn := fun m => rank_nullity_Fsub (k := k) ψ hψ hI m
    have hbound := rank_bound_Fsub (k := k) ψ v hspan hvI hn
    set H : ℕ → ℤ := fun m => (idim k I m : ℤ) with hH
    set Q : ℕ → ℤ := fun m => (qdim k I m : ℤ) with hQ
    set D : ℕ → ℤ := fun m => (Module.finrank k ↥(Fsub ψ I m) : ℤ) with hD
    have hQH : ∀ m, Q m + H m = (Module.finrank k B : ℤ) := by
      intro m
      have := qdim_add_idim (k := k) I m
      simp only [Q, H]
      push_cast
      omega
    have hrnZ : ∀ m, H (m + 1) + D m = (d : ℤ) * H m := by
      intro m
      have := hrn m
      simp only [H, D]
      push_cast
      omega
    have htelescope : ∀ (f : ℕ → ℤ) (m : ℕ),
        ∑ j ∈ Finset.range m, (f j - f (j + 1)) = f 0 - f m := by
      intro f m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    have hstep : ∀ j, D j - D (j + 1) =
        (d : ℤ) * (H j - H (j + 1)) - (H (j + 1) - H (j + 2)) := by
      intro j
      have h1 := hrnZ j
      have h2 := hrnZ (j + 1)
      linarith
    have hD1 : D 0 - D n =
        ∑ j ∈ Finset.range n, ((d : ℤ) * (H j - H (j + 1)) - (H (j + 1) - H (j + 2))) := by
      rw [← htelescope D n]
      exact (Finset.sum_congr rfl (fun j _ => (hstep j).symm)).symm
    have hD2 : ∑ j ∈ Finset.range n,
        ((d : ℤ) * (H j - H (j + 1)) - (H (j + 1) - H (j + 2))) =
        (d : ℤ) * (H 0 - H n) - (H 1 - H (n + 1)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      congr 1
      · rw [htelescope H n]
      · rw [htelescope (fun i => H (i + 1)) n]
    have hH0 : H 0 = (Module.finrank k B : ℤ) := by
      have h0 : idim k I 0 = Module.finrank k B := by
        rw [idim, Isub_zero, finrank_top]
      simp only [hH]
      rw [h0]
    have hQ1 : Q 1 = 1 := by
      simp only [hQ]
      rw [ha1]
      norm_num
    have hD3 : D 0 - D n = (d : ℤ) * Q n - (Q (n + 1) - 1) := by
      rw [hD1, hD2]
      have h1 := hQH n
      have h2 := hQH 1
      have h3 := hQH (n + 1)
      rw [← hH0] at h1
      rw [hQ1] at h2
      have ha : H 0 - H n = Q n := by linarith
      have hb : H 1 - H (n + 1) = Q (n + 1) - 1 := by linarith
      rw [ha, hb]
    have hbd : D 0 - D n ≤ (r : ℤ) * Q (n - 1) := by
      have hle' : Module.finrank k ↥(Fsub ψ I n) ≤ Module.finrank k ↥(Fsub ψ I 0) := by
        rw [show Module.finrank k ↥(Fsub ψ I n)
              = Module.finrank k ↥(Submodule.restrictScalars k (Fsub ψ I n)) from rfl,
            show Module.finrank k ↥(Fsub ψ I 0)
              = Module.finrank k ↥(Submodule.restrictScalars k (Fsub ψ I 0)) from rfl]
        exact Submodule.finrank_mono
          (Submodule.restrictScalars_mono k (Fsub_anti ψ I (Nat.zero_le n)))
      have hD0 : D 0 = (Module.finrank k ↥(Fsub ψ I 0) : ℤ) := by simp only [hD]
      have hDn : D n = (Module.finrank k ↥(Fsub ψ I n) : ℤ) := by simp only [hD]
      have hQn : Q (n - 1) = (qdim k I (n - 1) : ℤ) := by simp only [hQ]
      rw [hD0, hDn, hQn]
      push_cast
      exact_mod_cast hbound
    have hkey : (d : ℤ) * Q n + 1 ≤ Q (n + 1) + (r : ℤ) * Q (n - 1) := by
      linarith [hD3, hbd]
    have hcast : (d : ℤ) * (qdim k I n : ℤ) + 1 ≤
        (qdim k I (n + 1) : ℤ) + (r : ℤ) * (qdim k I (n - 1) : ℤ) := hkey
    exact_mod_cast hcast
  exact gs_series_aux hd ha0 ha1 hmono hstab hineq

end

end Work.GolodShafarevich.AbstractGS




