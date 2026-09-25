import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_degree_right_mul_finrank
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_ideal_degree_le
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_quotient_map_equiv
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_relator_right_mul_finrank_sum_le
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_submodule_finite_of_le_gradedPart
import Submission.Commons.LinearAlgebra.Quotient.finrank_quotient_le_of_le
import Submission.Commons.LinearAlgebra.Submodule.finrank_iSup_le_sum_of_finite

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra
open scoped BigOperators

set_option linter.style.haveILetI false in
theorem golod_shafarevich_fundamental_inequality
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      degreeSubmodule (degRel r))
    (n : ℕ) (hn : 0 < n) :
    let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
      Submodule.span K {x | ∃ w : FreeMonoid ι,
        (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
    let twoSidedSpan : (σ → FreeAlgebra K ι) → Submodule K (FreeAlgebra K ι) := fun rel =>
      Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
        x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}
    let b : ℕ → ℕ := fun n =>
      Module.finrank K
        (Submodule.map (Submodule.mkQ (twoSidedSpan rel)) (degreeSubmodule n))
    Fintype.card ι * b (n - 1) ≤
      b n + ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 := by
  change Fintype.card ι *
      (fun m : ℕ => Module.finrank K
        (Submodule.map (Submodule.mkQ (golodShafarevich_twoSidedIdeal K ι σ rel))
          (golodShafarevich_gradedPart K ι m))) (n - 1) ≤
    (fun m : ℕ => Module.finrank K
        (Submodule.map (Submodule.mkQ (golodShafarevich_twoSidedIdeal K ι σ rel))
          (golodShafarevich_gradedPart K ι m))) n +
      ∑ r : σ, if degRel r ≤ n then
        (fun m : ℕ => Module.finrank K
          (Submodule.map (Submodule.mkQ (golodShafarevich_twoSidedIdeal K ι σ rel))
            (golodShafarevich_gradedPart K ι m))) (n - degRel r) else 0

  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let b : ℕ → ℕ := fun n => Module.finrank K (Submodule.map I.mkQ (V n))
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let S : σ → Submodule K (FreeAlgebra K ι) := fun r =>
    Submodule.span K {x | ∃ a ∈ V (n - degRel r), x = a * rel r}
  let S_all := Submodule.span K {x | ∃ r : σ, degRel r ≤ n ∧ ∃ a ∈ V (n - degRel r), x = a * rel r}
  have hVn_fin : Module.Finite K ↥(V n) := by
    dsimp [V]
    exact golodShafarevich_gradedPart_finiteDimensional (K := K) (ι := ι) n
  haveI : Module.Finite K ↥(V n) := hVn_fin
  have hT_le_Vn : T ≤ V n := by
    dsimp [T, V]
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨a, ha, i, rfl⟩
    have haV : a ∈ golodShafarevich_gradedPart K ι (n - 1) := ha.2
    have hbV : FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) ∈ golodShafarevich_gradedPart K ι 1 := by
      simpa [FreeMonoid.length_of] using
        (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) (FreeMonoid.of i))
    have hprod := golodShafarevich_gradedPart_mul_mem (K := K) (ι := ι) haV hbV
    simpa [Nat.sub_one_add_one_eq_of_pos hn] using hprod
  have hS_le_Vn : S_all ≤ V n := by
    dsimp [S_all, V]
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨r, hrn, a, haV, rfl⟩
    have hrelV : rel r ∈ golodShafarevich_gradedPart K ι (degRel r) := hhom r
    have hprod := golodShafarevich_gradedPart_mul_mem (K := K) (ι := ι) haV hrelV
    have hsum : (n - degRel r) + degRel r = n := Nat.sub_add_cancel hrn
    simpa [hsum] using hprod
  have hTS_le_Vn : T ⊔ S_all ≤ V n := sup_le hT_le_Vn hS_le_Vn
  have hT_fin : Module.Finite K ↥T :=
    Commons.Algebra.FreeAlgebra.golod_shafarevich_submodule_finite_of_le_gradedPart n T hT_le_Vn
  have hS_fin : Module.Finite K ↥S_all :=
    Commons.Algebra.FreeAlgebra.golod_shafarevich_submodule_finite_of_le_gradedPart n S_all hS_le_Vn
  have hTS_fin : Module.Finite K ↥(T ⊔ S_all) :=
    Commons.Algebra.FreeAlgebra.golod_shafarevich_submodule_finite_of_le_gradedPart n (T ⊔ S_all) hTS_le_Vn
  haveI : Module.Finite K ↥T := hT_fin
  haveI : Module.Finite K ↥S_all := hS_fin
  haveI : Module.Finite K ↥(T ⊔ S_all) := hTS_fin
  have hI_le_TS : I ⊓ V n ≤ T ⊔ S_all := by
    dsimp [I, T, S_all, V]
    exact golod_shafarevich_ideal_degree_le (K := K) (ι := ι) (σ := σ) degRel rel hhom n hn
  have hdeg_right := golod_shafarevich_degree_right_mul_finrank (K := K) (ι := ι) (σ := σ) degRel rel n hn
  have hdeg_right' : Module.finrank K (Submodule.map T.mkQ (V n)) =
      Fintype.card ι * b (n - 1) := by
    simpa [b, V, I, T] using hdeg_right
  have hmap_T_Sall : Submodule.map T.mkQ S_all = Submodule.map T.mkQ (T ⊔ S_all) := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  -- finite sum bound for the relator part
  let σn := {r : σ // degRel r ≤ n}
  let F : σn → Submodule K (FreeAlgebra K ι ⧸ T) := fun r => Submodule.map T.mkQ (S r.1)
  haveI : ∀ r : σn, Module.Finite K ↥(F r) := by
    intro r
    have hSr_le_Vn : S r.1 ≤ V n := by
      dsimp [S, V]
      rw [Submodule.span_le]
      intro x hx
      rcases hx with ⟨a, haV, rfl⟩
      have hrelV : rel r.1 ∈ golodShafarevich_gradedPart K ι (degRel r.1) := hhom r.1
      have hprod := golodShafarevich_gradedPart_mul_mem (K := K) (ι := ι) haV hrelV
      have hsum : (n - degRel r.1) + degRel r.1 = n := Nat.sub_add_cancel r.2
      simpa [hsum] using hprod
    have hSr_fin : Module.Finite K ↥(S r.1) :=
      Commons.Algebra.FreeAlgebra.golod_shafarevich_submodule_finite_of_le_gradedPart n (S r.1) hSr_le_Vn
    dsimp [F]
    exact Module.Finite.map (p := S r.1) (f := T.mkQ)
  have hS_all_le_iSup : S_all ≤ ⨆ r : σn, S r.1 := by
    dsimp [S_all]
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨r, hrn, a, haV, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨r, hrn⟩ ?_
    apply Submodule.subset_span
    exact ⟨a, haV, rfl⟩
  have hmap_le : Submodule.map T.mkQ S_all ≤ ⨆ r : σn, F r := by
    have h := Submodule.map_mono (f := T.mkQ) hS_all_le_iSup
    have hmap_iSup := Submodule.map_iSup (f := T.mkQ) (σ₁₂ := RingHom.id K)
      (p := fun r : σn => S r.1)
    rw [hmap_iSup] at h
    simpa [F] using h
  have hfin_iSup := Commons.LinearAlgebra.Submodule.finrank_iSup_le_sum_of_finite
    (K := K) (V := FreeAlgebra K ι ⧸ T) (ι := σn) (S := F)
  have hle_map : Module.finrank K (Submodule.map T.mkQ S_all) ≤
      Module.finrank K ↥(⨆ r : σn, F r) := Submodule.finrank_mono hmap_le
  have hsum_sub : (∑ r : σn, Module.finrank K ↥(F r)) =
      ∑ r : σ, if degRel r ≤ n then Module.finrank K (Submodule.map T.mkQ (S r)) else 0 := by
    dsimp [F]
    classical
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (s := Finset.univ.filter (fun r : σ => degRel r ≤ n))
      (p := fun r : σ => degRel r ≤ n) (fun x => by simp [Finset.mem_filter])
      (fun r : σ => Module.finrank K (Submodule.map T.mkQ (S r)))).symm
  have hSall_map_le_sum : Module.finrank K (Submodule.map T.mkQ S_all) ≤
      ∑ r : σ, if degRel r ≤ n then Module.finrank K (Submodule.map T.mkQ (S r)) else 0 := by
    exact le_trans hle_map (by simpa [hsum_sub] using hfin_iSup)
  have hsum_rel := golod_shafarevich_relator_right_mul_finrank_sum_le (K := K) (ι := ι) (σ := σ)
    degRel rel hdeg hhom n hn
  have hrel_le : (∑ r : σ, if degRel r ≤ n then Module.finrank K (Submodule.map T.mkQ (S r)) else 0) ≤
      ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 := by
    simpa [b, V, I, T, S] using hsum_rel
  have hSall_rel : Module.finrank K (Submodule.map T.mkQ S_all) ≤
      ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 :=
    le_trans hSall_map_le_sum hrel_le
  -- quotient monotonicity term
  let ATS : Submodule K ↥(V n) := Submodule.comap (V n).subtype (T ⊔ S_all)
  let AI : Submodule K ↥(V n) := Submodule.comap (V n).subtype I
  have hAI_le_ATS : AI ≤ ATS := by
    intro x hx
    rw [Submodule.mem_comap] at hx ⊢
    exact hI_le_TS ⟨hx, x.2⟩
  have hquot_le : Module.finrank K (↥(V n) ⧸ ATS) ≤ b n := by
    have hq := Commons.LinearAlgebra.Quotient.finrank_quotient_le_of_le (K := K) (V := ↥(V n)) hAI_le_ATS
    have hb : b n = Module.finrank K (↥(V n) ⧸ AI) := by
      dsimp [b, V, I, AI]
      obtain ⟨e⟩ := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) I (V n)
      exact LinearEquiv.finrank_eq e
    rw [hb]
    exact hq
  -- rank-nullity arithmetic
  have hmap_VT : Module.finrank K (Submodule.map T.mkQ (V n)) =
      Module.finrank K ↥(V n) - Module.finrank K T := by
    obtain ⟨e⟩ := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) T (V n)
    have hq : Module.finrank K (Submodule.map T.mkQ (V n)) =
        Module.finrank K (↥(V n) ⧸ Submodule.comap (V n).subtype T) :=
      LinearEquiv.finrank_eq e
    have hker : Module.finrank K ↥(Submodule.comap (V n).subtype T) = Module.finrank K ↥T :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hT_le_Vn)
    have hrank := Submodule.finrank_quotient_add_finrank (R := K) (M := ↥(V n)) (Submodule.comap (V n).subtype T)
    rw [hker] at hrank
    omega
  have hmap_W : Module.finrank K (Submodule.map T.mkQ (T ⊔ S_all)) =
      Module.finrank K ↥(T ⊔ S_all) - Module.finrank K T := by
    obtain ⟨e⟩ := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) T (T ⊔ S_all)
    have hq : Module.finrank K (Submodule.map T.mkQ (T ⊔ S_all)) =
        Module.finrank K (↥(T ⊔ S_all) ⧸ Submodule.comap (T ⊔ S_all).subtype T) :=
      LinearEquiv.finrank_eq e
    have hker : Module.finrank K ↥(Submodule.comap (T ⊔ S_all).subtype T) = Module.finrank K ↥T :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := T) (q := T ⊔ S_all) le_sup_left)
    have hrank := Submodule.finrank_quotient_add_finrank (R := K) (M := ↥(T ⊔ S_all)) (Submodule.comap (T ⊔ S_all).subtype T)
    rw [hker] at hrank
    omega
  have hmap_TS : Module.finrank K (Submodule.map T.mkQ S_all) =
      Module.finrank K ↥(T ⊔ S_all) - Module.finrank K T := by
    rw [hmap_T_Sall]
    exact hmap_W
  have hATS_fin : Module.finrank K ATS = Module.finrank K ↥(T ⊔ S_all) := by
    dsimp [ATS]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := T ⊔ S_all) (q := V n) hTS_le_Vn)
  have hquot_fin : Module.finrank K (↥(V n) ⧸ ATS) =
      Module.finrank K ↥(V n) - Module.finrank K ↥(T ⊔ S_all) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := ↥(V n)) ATS
    rw [hATS_fin] at h
    omega
  have harith : Module.finrank K (Submodule.map T.mkQ (V n)) =
      Module.finrank K (Submodule.map T.mkQ S_all) + Module.finrank K (↥(V n) ⧸ ATS) := by
    rw [hmap_VT, hmap_TS, hquot_fin]
    have hl_le_m : Module.finrank K ↥T ≤ Module.finrank K ↥(T ⊔ S_all) :=
      Submodule.finrank_mono le_sup_left
    have hm_le_k : Module.finrank K ↥(T ⊔ S_all) ≤ Module.finrank K ↥(V n) :=
      Submodule.finrank_mono hTS_le_Vn
    omega
  have hmain_le : Fintype.card ι * b (n - 1) ≤
      b n + ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 := by
    rw [← hdeg_right']
    rw [harith]
    have h1 : Module.finrank K (Submodule.map T.mkQ S_all) ≤
        ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 := hSall_rel
    have h2 : Module.finrank K (↥(V n) ⧸ ATS) ≤ b n := hquot_le
    omega
  simpa [b, V, I] using hmain_le

end Commons.Algebra.FreeAlgebra
