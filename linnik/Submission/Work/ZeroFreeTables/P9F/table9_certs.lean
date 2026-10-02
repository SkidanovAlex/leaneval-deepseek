/-
# ZeroFreeTables.P9F.table9_certs

Numerical certificates for the twenty rows of HB Table 9 (the `F`-method,
Lemma 9.2).  Each row lemma shows that the F-inequality of Lemma 9.2 fails at the
tabulated point, given only the (rational) range of the test-function parameter `θ`
with `tan θ = T` and rational enclosures of the two exponentials `tf71Ec`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Defs
import Submission.Work.ZeroFreeTables.P9F.tf71Fr_bilinear

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

theorem coefA_034_1283 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (21/500) (-17/50 : ℝ) = (286012471615731/428808839290 : ℝ) ∧
    tf71P10 θ (21/500) (-17/50 : ℝ) = (-4916722314/25884625 : ℝ) ∧
    tf71P01 θ (21/500) (-17/50 : ℝ) = (33785788728825/85761767858 : ℝ) ∧
    tf71P11 θ (21/500) (-17/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_034_1283 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (21/500) (943/1000 : ℝ) = (434666786860268257932/3527707765187560249 : ℝ) ∧
    tf71P10 θ (21/500) (943/1000 : ℝ) = (14740698456624/46955482675 : ℝ) ∧
    tf71P01 θ (21/500) (943/1000 : ℝ) = (738250909180312500000/3527707765187560249 : ℝ) ∧
    tf71P11 θ (21/500) (943/1000 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_034_1283 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (6737422233/2500000000 : ℝ) ≤ tf71Ec θ (21/500 : ℝ) (-17/50 : ℝ))
    (hE1hi : tf71Ec θ (21/500 : ℝ) (-17/50 : ℝ) ≤ (2694968893201/1000000000000 : ℝ))
    (hE2lo : (500000000000/7818501284589 : ℝ) ≤ tf71Ec θ (21/500 : ℝ) (943/1000 : ℝ))
    (hE2hi : tf71Ec θ (21/500 : ℝ) (943/1000 : ℝ) ≤ (1000000000000/15637002569177 : ℝ))
    :
    ((81/100 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (21/500 : ℝ) (-17/50 : ℝ) - tf71Fr θ (21/500 : ℝ) (943/1000 : ℝ))
      - 2 * (81/100 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((17987/20000 : ℝ) + ((53961/10000 : ℝ)) * (1/1000000 : ℝ) + ((11561/10000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((21/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-17/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_034_1283 θ htan
  have hz2 : ((943/1000 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_034_1283 θ htan
  have hΦ1 : tf71Fr θ (21/500 : ℝ) (-17/50 : ℝ) ≤ (2875797868951/2000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (21/500 : ℝ) (-17/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (1542916535889/2500000000 : ℝ) ≤ tf71Fr θ (21/500 : ℝ) (943/1000 : ℝ) := by
    rw [tf71Fr_bilinear θ (21/500 : ℝ) (943/1000 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (145650035225315432721/156250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_036_123 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (21/500) (-9/25 : ℝ) = (437311814611/674697960 : ℝ) ∧
    tf71P10 θ (21/500) (-9/25 : ℝ) = (-101752231/513375 : ℝ) ∧
    tf71P01 θ (21/500) (-9/25 : ℝ) = (52775000425/134939592 : ℝ) ∧
    tf71P11 θ (21/500) (-9/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_036_123 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (21/500) (87/100 : ℝ) = (658826774249/4487109245 : ℝ) ∧
    tf71P10 θ (21/500) (87/100 : ℝ) = (1162540218/3744625 : ℝ) ∧
    tf71P01 θ (21/500) (87/100 : ℝ) = (217036954400/897421849 : ℝ) ∧
    tf71P11 θ (21/500) (87/100 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_036_123 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (2856804019657/1000000000000 : ℝ) ≤ tf71Ec θ (21/500 : ℝ) (-9/25 : ℝ))
    (hE1hi : tf71Ec θ (21/500 : ℝ) (-9/25 : ℝ) ≤ (1428402009829/500000000000 : ℝ))
    (hE2lo : (1000000000000/12638952547029 : ℝ) ≤ tf71Ec θ (21/500 : ℝ) (87/100 : ℝ))
    (hE2hi : tf71Ec θ (21/500 : ℝ) (87/100 : ℝ) ≤ (1000000000000/12638952547027 : ℝ))
    :
    ((407/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (21/500 : ℝ) (-9/25 : ℝ) - tf71Fr θ (21/500 : ℝ) (87/100 : ℝ))
      - 2 * (407/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((1354649/1500000 : ℝ) + ((1354649/250000 : ℝ)) * (1/1000000 : ℝ) + ((290649/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((21/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-9/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_036_123 θ htan
  have hz2 : ((87/100 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_036_123 θ htan
  have hΦ1 : tf71Fr θ (21/500 : ℝ) (-9/25 : ℝ) ≤ (7310230768471/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (21/500 : ℝ) (-9/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (6412125199443/10000000000 : ℝ) ≤ tf71Fr θ (21/500 : ℝ) (87/100 : ℝ) := by
    rw [tf71Fr_bilinear θ (21/500 : ℝ) (87/100 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (21/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (145650035225315432721/156250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_038_1181 (θ : ℝ) (htan : Real.tan θ = 24/1) :
    tf71P00 θ (9/200) (-19/50 : ℝ) = (9221131503945/15506724676 : ℝ) ∧
    tf71P10 θ (9/200) (-19/50 : ℝ) = (-371907081/1992416 : ℝ) ∧
    tf71P01 θ (9/200) (-19/50 : ℝ) = (1376513500473/3876681169 : ℝ) ∧
    tf71P11 θ (9/200) (-19/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_038_1181 (θ : ℝ) (htan : Real.tan θ = 24/1) :
    tf71P00 θ (9/200) (801/1000 : ℝ) = (643478725108905/3946456391761 : ℝ) ∧
    tf71P10 θ (9/200) (801/1000 : ℝ) = (4438148405/15892552 : ℝ) ∧
    tf71P01 θ (9/200) (801/1000 : ℝ) = (1057198417920000/3946456391761 : ℝ) ∧
    tf71P11 θ (9/200) (801/1000 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_038_1181 {θ : ℝ}
    (h1 : (15291537476963/10000000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (152915374769631/100000000000000 : ℝ))
    (htan : Real.tan θ = 24/1)
    (hE1lo : (2933133060883/1000000000000 : ℝ) ≤ tf71Ec θ (9/200 : ℝ) (-19/50 : ℝ))
    (hE1hi : tf71Ec θ (9/200 : ℝ) (-19/50 : ℝ) ≤ (733283265221/250000000000 : ℝ))
    (hE2lo : (1000000000000/9662425713401 : ℝ) ≤ tf71Ec θ (9/200 : ℝ) (801/1000 : ℝ))
    (hE2hi : tf71Ec θ (9/200 : ℝ) (801/1000 : ℝ) ≤ (5000000000/48312128567 : ℝ))
    :
    ((817/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (9/200 : ℝ) (-19/50 : ℝ) - tf71Fr θ (9/200 : ℝ) (801/1000 : ℝ))
      - 2 * (817/1000 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (9/200 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((5435489/6000000 : ℝ) + ((5435489/1000000 : ℝ)) * (1/1000000 : ℝ) + ((1167489/1000000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((9/200 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-19/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_038_1181 θ htan
  have hz2 : ((801/1000 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_038_1181 θ htan
  have hΦ1 : tf71Fr θ (9/200 : ℝ) (-19/50 : ℝ) ≤ (13507027291663/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (9/200 : ℝ) (-19/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (6178076692099/10000000000 : ℝ) ≤ tf71Fr θ (9/200 : ℝ) (801/1000 : ℝ) := by
    rw [tf71Fr_bilinear θ (9/200 : ℝ) (801/1000 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (323721959285583384320071840949433/320000000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (9/200 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (140796081447487900119/160000000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_04_1135 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (11/250) (-2/5 : ℝ) = (58950870407/93845000 : ℝ) ∧
    tf71P10 θ (11/250) (-2/5 : ℝ) = (-3542847/17125 : ℝ) ∧
    tf71P01 θ (11/250) (-2/5 : ℝ) = (36299035993/93845000 : ℝ) ∧
    tf71P11 θ (11/250) (-2/5 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_04_1135 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (11/250) (147/200 : ℝ) = (112058511467489576/529556645451645 : ℝ) ∧
    tf71P10 θ (11/250) (147/200 : ℝ) = (376450789088/1286415375 : ℝ) ∧
    tf71P01 θ (11/250) (147/200 : ℝ) = (35595898782118400/105911329090329 : ℝ) ∧
    tf71P11 θ (11/250) (147/200 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_04_1135 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (761113762601/250000000000 : ℝ) ≤ tf71Ec θ (11/250 : ℝ) (-2/5 : ℝ))
    (hE1hi : tf71Ec θ (11/250 : ℝ) (-2/5 : ℝ) ≤ (608891010081/200000000000 : ℝ))
    (hE2lo : (1000000000000/7734795361959 : ℝ) ≤ tf71Ec θ (11/250 : ℝ) (147/200 : ℝ))
    (hE2hi : tf71Ec θ (11/250 : ℝ) (147/200 : ℝ) ≤ (500000000000/3867397680979 : ℝ))
    :
    ((41/50 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (11/250 : ℝ) (-2/5 : ℝ) - tf71Fr θ (11/250 : ℝ) (147/200 : ℝ))
      - 2 * (41/50 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (11/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((13631/15000 : ℝ) + ((13631/2500 : ℝ)) * (1/1000000 : ℝ) + ((2931/2500 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((11/250 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-2/5 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_04_1135 θ htan
  have hz2 : ((147/200 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_04_1135 θ htan
  have hΦ1 : tf71Fr θ (11/250 : ℝ) (-2/5 : ℝ) ≤ (2978126339431/2000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (11/250 : ℝ) (-2/5 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (54924345861/78125000 : ℝ) ≤ tf71Fr θ (11/250 : ℝ) (147/200 : ℝ) := by
    rw [tf71Fr_bilinear θ (11/250 : ℝ) (147/200 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (11/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (76292875594212845711/78125000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_042_1094 (θ : ℝ) (htan : Real.tan θ = 24/1) :
    tf71P00 θ (23/500) (-21/50 : ℝ) = (1178687603249101/2069981698050 : ℝ) ∧
    tf71P10 θ (23/500) (-21/50 : ℝ) = (-9637440013/48832560 : ℝ) ∧
    tf71P01 θ (23/500) (-21/50 : ℝ) = (361368542658112/1034990849025 : ℝ) ∧
    tf71P11 θ (23/500) (-21/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_042_1094 (θ : ℝ) (htan : Real.tan θ = 24/1) :
    tf71P00 θ (23/500) (337/500 : ℝ) = (4278362821913147115/19869158045916001 : ℝ) ∧
    tf71P10 θ (23/500) (337/500 : ℝ) = (293580438263/1127664008 : ℝ) ∧
    tf71P01 θ (23/500) (337/500 : ℝ) = (6942839499502387200/19869158045916001 : ℝ) ∧
    tf71P11 θ (23/500) (337/500 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_042_1094 {θ : ℝ}
    (h1 : (15291537476963/10000000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (152915374769631/100000000000000 : ℝ))
    (htan : Real.tan θ = 24/1)
    (hE1lo : (1600537269953/500000000000 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (-21/50 : ℝ))
    (hE1hi : tf71Ec θ (23/500 : ℝ) (-21/50 : ℝ) ≤ (3201074539907/1000000000000 : ℝ))
    (hE2lo : (500000000000/3234814895597 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (337/500 : ℝ))
    (hE2hi : tf71Ec θ (23/500 : ℝ) (337/500 : ℝ) ≤ (1000000000000/6469629791193 : ℝ))
    :
    ((411/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) (-21/50 : ℝ) - tf71Fr θ (23/500 : ℝ) (337/500 : ℝ))
      - 2 * (411/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((455307/500000 : ℝ) + ((1365921/250000 : ℝ)) * (1/1000000 : ℝ) + ((293921/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((23/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-21/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_042_1094 θ htan
  have hz2 : ((337/500 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_042_1094 θ htan
  have hΦ1 : tf71Fr θ (23/500 : ℝ) (-21/50 : ℝ) ≤ (6926450760859/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (-21/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (1668607936707/2500000000 : ℝ) ≤ tf71Fr θ (23/500 : ℝ) (337/500 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (337/500 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (323721959285583384320071840949433/320000000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (359812208143580189193/400000000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_044_1055 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (23/500) (-11/25 : ℝ) = (679042815535603/1112502657640 : ℝ) ∧
    tf71P10 θ (23/500) (-11/25 : ℝ) = (-4471507671/20846375 : ℝ) ∧
    tf71P01 θ (23/500) (-11/25 : ℝ) = (84982233812425/222500531528 : ℝ) ∧
    tf71P11 θ (23/500) (-11/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_044_1055 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (23/500) (123/200 : ℝ) = (95345020304560916/350080887497445 : ℝ) ∧
    tf71P10 θ (23/500) (123/200 : ℝ) = (276637758352/1045945875 : ℝ) ∧
    tf71P01 θ (23/500) (123/200 : ℝ) = (30616009754074400/70016177499489 : ℝ) ∧
    tf71P11 θ (23/500) (123/200 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_044_1055 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (322653330539/100000000000 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (-11/25 : ℝ))
    (hE1hi : tf71Ec θ (23/500 : ℝ) (-11/25 : ℝ) ≤ (3226533305391/1000000000000 : ℝ))
    (hE2lo : (500000000000/2570658575151 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (123/200 : ℝ))
    (hE2hi : tf71Ec θ (23/500 : ℝ) (123/200 : ℝ) ≤ (1000000000000/5141317150301 : ℝ))
    :
    ((33/40 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) (-11/25 : ℝ) - tf71Fr θ (23/500 : ℝ) (123/200 : ℝ))
      - 2 * (33/40 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((2923/3200 : ℝ) + ((8769/1600 : ℝ)) * (1/1000000 : ℝ) + ((1889/1600 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((23/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-11/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_044_1055 θ htan
  have hz2 : ((123/200 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_044_1055 θ htan
  have hΦ1 : tf71Fr θ (23/500 : ℝ) (-11/25 : ℝ) ≤ (3028728591253/2000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (-11/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (762281111801/1000000000 : ℝ) ≤ tf71Fr θ (23/500 : ℝ) (123/200 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (123/200 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (159521467151535950123/156250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_046_1018 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (23/500) (-23/50 : ℝ) = (4998923/8410 : ℝ) ∧
    tf71P10 θ (23/500) (-23/50 : ℝ) = (-801906/3625 : ℝ) ∧
    tf71P01 θ (23/500) (-23/50 : ℝ) = (633825/1682 : ℝ) ∧
    tf71P11 θ (23/500) (-23/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_046_1018 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (23/500) (279/500 : ℝ) = (955571024016417211/3246835158734049 : ℝ) ∧
    tf71P10 θ (23/500) (279/500 : ℝ) = (356677320202/1424525175 : ℝ) ∧
    tf71P01 θ (23/500) (279/500 : ℝ) = (1560269455182031250/3246835158734049 : ℝ) ∧
    tf71P11 θ (23/500) (279/500 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_046_1018 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (3402988825309/1000000000000 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (-23/50 : ℝ))
    (hE1hi : tf71Ec θ (23/500 : ℝ) (-23/50 : ℝ) ≤ (340298882531/100000000000 : ℝ))
    (hE2lo : (100000000000/441743266967 : ℝ) ≤ tf71Ec θ (23/500 : ℝ) (279/500 : ℝ))
    (hE2hi : tf71Ec θ (23/500 : ℝ) (279/500 : ℝ) ≤ (1000000000000/4417432669669 : ℝ))
    :
    ((207/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (23/500 : ℝ) (-23/50 : ℝ) - tf71Fr θ (23/500 : ℝ) (279/500 : ℝ))
      - 2 * (207/250 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((114533/125000 : ℝ) + ((343599/62500 : ℝ)) * (1/1000000 : ℝ) + ((74099/62500 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((23/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-23/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_046_1018 θ htan
  have hz2 : ((279/500 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_046_1018 θ htan
  have hΦ1 : tf71Fr θ (23/500 : ℝ) (-23/50 : ℝ) ≤ (7690519184687/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (-23/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (3931923660713/5000000000 : ℝ) ≤ tf71Fr θ (23/500 : ℝ) (279/500 : ℝ) := by
    rw [tf71Fr_bilinear θ (23/500 : ℝ) (279/500 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (23/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (159521467151535950123/156250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_048_0984 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (47/1000) (-12/25 : ℝ) = (56133570378812683/95676882762240 : ℝ) ∧
    tf71P10 θ (47/1000) (-12/25 : ℝ) = (-43383459839/193323000 : ℝ) ∧
    tf71P01 θ (47/1000) (-12/25 : ℝ) = (7158986948645425/19135376552448 : ℝ) ∧
    tf71P11 θ (47/1000) (-12/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_048_0984 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (47/1000) (63/125 : ℝ) = (107530764881943872183/339371878667478048 : ℝ) ∧
    tf71P10 θ (47/1000) (63/125 : ℝ) = (1193674798439/5149119150 : ℝ) ∧
    tf71P01 θ (47/1000) (63/125 : ℝ) = (181133592887091015625/339371878667478048 : ℝ) ∧
    tf71P11 θ (47/1000) (63/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_048_0984 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (3492824014431/1000000000000 : ℝ) ≤ tf71Ec θ (47/1000 : ℝ) (-12/25 : ℝ))
    (hE1hi : tf71Ec θ (47/1000 : ℝ) (-12/25 : ℝ) ≤ (109150750451/31250000000 : ℝ))
    (hE2lo : (500000000000/1859111956089 : ℝ) ≤ tf71Ec θ (47/1000 : ℝ) (63/125 : ℝ))
    (hE2hi : tf71Ec θ (47/1000 : ℝ) (63/125 : ℝ) ≤ (1000000000000/3718223912177 : ℝ))
    :
    ((104/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (47/1000 : ℝ) (-12/25 : ℝ) - tf71Fr θ (47/1000 : ℝ) (63/125 : ℝ))
      - 2 * (104/125 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (47/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((172507/187500 : ℝ) + ((172507/31250 : ℝ)) * (1/1000000 : ℝ) + ((37257/31250 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((47/1000 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-12/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_048_0984 θ htan
  have hz2 : ((63/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_048_0984 θ htan
  have hΦ1 : tf71Fr θ (47/1000 : ℝ) (-12/25 : ℝ) ≤ (7749580467967/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (47/1000 : ℝ) (-12/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (8152730895553/10000000000 : ℝ) ≤ tf71Fr θ (47/1000 : ℝ) (63/125 : ℝ) := by
    rw [tf71Fr_bilinear θ (47/1000 : ℝ) (63/125 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (47/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (325978650266182158947/312500000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_05_0952 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (-1/2 : ℝ) = (258559607016/446265625 : ℝ) ∧
    tf71P10 θ (6/125) (-1/2 : ℝ) = (-120101856/528125 : ℝ) ∧
    tf71P01 θ (6/125) (-1/2 : ℝ) = (165751017984/446265625 : ℝ) ∧
    tf71P11 θ (6/125) (-1/2 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_05_0952 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (113/250 : ℝ) = (44972077589192952/134859376732609 : ℝ) ∧
    tf71P10 θ (6/125) (113/250 : ℝ) = (61590377184/290322425 : ℝ) ∧
    tf71P01 θ (6/125) (113/250 : ℝ) = (79228125000000000/134859376732609 : ℝ) ∧
    tf71P11 θ (6/125) (113/250 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_05_0952 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (716228129577/200000000000 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (-1/2 : ℝ))
    (hE1hi : tf71Ec θ (6/125 : ℝ) (-1/2 : ℝ) ≤ (1790570323943/500000000000 : ℝ))
    (hE2lo : (50000000000/158418293289 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (113/250 : ℝ))
    (hE2hi : tf71Ec θ (6/125 : ℝ) (113/250 : ℝ) ≤ (1000000000000/3168365865779 : ℝ))
    :
    ((417/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) (-1/2 : ℝ) - tf71Fr θ (6/125 : ℝ) (113/250 : ℝ))
      - 2 * (417/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((460963/500000 : ℝ) + ((1382889/250000 : ℝ)) * (1/1000000 : ℝ) + ((298889/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((6/125 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-1/2 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_05_0952 θ htan
  have hz2 : ((113/250 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_05_0952 θ htan
  have hΦ1 : tf71Fr θ (6/125 : ℝ) (-1/2 : ℝ) ≤ (15613585549679/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (-1/2 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (4218257430903/5000000000 : ℝ) ≤ tf71Fr θ (6/125 : ℝ) (113/250 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (113/250 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (20807147889330776103/19531250000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_052_0922 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (-13/25 : ℝ) = (545233651524/965633045 : ℝ) ∧
    tf71P10 θ (6/125) (-13/25 : ℝ) = (-405392592/1737125 : ℝ) ∧
    tf71P01 θ (6/125) (-13/25 : ℝ) = (70603034400/193126609 : ℝ) ∧
    tf71P11 θ (6/125) (-13/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_052_0922 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (201/500 : ℝ) = (3036836299592432/8884948062169 : ℝ) ∧
    tf71P10 θ (6/125) (201/500 : ℝ) = (14518652736/74519075 : ℝ) ∧
    tf71P01 θ (6/125) (201/500 : ℝ) = (5634000000000000/8884948062169 : ℝ) ∧
    tf71P11 θ (6/125) (201/500 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_052_0922 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (3768618998851/1000000000000 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (-13/25 : ℝ))
    (hE1hi : tf71Ec θ (6/125 : ℝ) (-13/25 : ℝ) ≤ (942154749713/250000000000 : ℝ))
    (hE2lo : (200000000000/557780315549 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (201/500 : ℝ))
    (hE2hi : tf71Ec θ (6/125 : ℝ) (201/500 : ℝ) ≤ (62500000000/174306348609 : ℝ))
    :
    ((209/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) (-13/25 : ℝ) - tf71Fr θ (6/125 : ℝ) (201/500 : ℝ))
      - 2 * (209/250 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((115477/125000 : ℝ) + ((346431/62500 : ℝ)) * (1/1000000 : ℝ) + ((74931/62500 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((6/125 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-13/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_052_0922 θ htan
  have hz2 : ((201/500 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_052_0922 θ htan
  have hΦ1 : tf71Fr θ (6/125 : ℝ) (-13/25 : ℝ) ≤ (15851198844617/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (-13/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (433707297679/500000000 : ℝ) ≤ tf71Fr θ (6/125 : ℝ) (201/500 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (201/500 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (20807147889330776103/19531250000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_054_0893 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (-27/50 : ℝ) = (51550216088/93701205 : ℝ) ∧
    tf71P10 θ (6/125) (-27/50 : ℝ) = (-129376672/541125 : ℝ) ∧
    tf71P01 θ (6/125) (-27/50 : ℝ) = (6734758400/18740241 : ℝ) ∧
    tf71P11 θ (6/125) (-27/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_054_0893 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (6/125) (353/1000 : ℝ) = (104761289681476183008/305042996842878529 : ℝ) ∧
    tf71P10 θ (6/125) (353/1000 : ℝ) = (2437928013696/13807674425 : ℝ) ∧
    tf71P01 θ (6/125) (353/1000 : ℝ) = (208731532953600000000/305042996842878529 : ℝ) ∧
    tf71P11 θ (6/125) (353/1000 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_054_0893 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (3965912136649/1000000000000 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (-27/50 : ℝ))
    (hE1hi : tf71Ec θ (6/125 : ℝ) (-27/50 : ℝ) ≤ (3965912136651/1000000000000 : ℝ))
    (hE2lo : (1000000000000/2461155720431 : ℝ) ≤ tf71Ec θ (6/125 : ℝ) (353/1000 : ℝ))
    (hE2hi : tf71Ec θ (6/125 : ℝ) (353/1000 : ℝ) ≤ (100000000000/246115572043 : ℝ))
    :
    ((419/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (6/125 : ℝ) (-27/50 : ℝ) - tf71Fr θ (6/125 : ℝ) (353/1000 : ℝ))
      - 2 * (419/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((1388561/1500000 : ℝ) + ((1388561/250000 : ℝ)) * (1/1000000 : ℝ) + ((300561/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((6/125 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-27/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_054_0893 θ htan
  have hz2 : ((353/1000 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_054_0893 θ htan
  have hΦ1 : tf71Fr θ (6/125 : ℝ) (-27/50 : ℝ) ≤ (16094010346621/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (-27/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (8917449770649/10000000000 : ℝ) ≤ tf71Fr θ (6/125 : ℝ) (353/1000 : ℝ) := by
    rw [tf71Fr_bilinear θ (6/125 : ℝ) (353/1000 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (6/125 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (20807147889330776103/19531250000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_056_0866 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (49/1000) (-14/25 : ℝ) = (763679300923/1403751040 : ℝ) ∧
    tf71P10 θ (49/1000) (-14/25 : ℝ) = (-178805319/740500 : ℝ) ∧
    tf71P01 θ (49/1000) (-14/25 : ℝ) = (100120319425/280750208 : ℝ) ∧
    tf71P11 θ (49/1000) (-14/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_056_0866 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (49/1000) (153/500 : ℝ) = (39748495854164943839/118995818796912978 : ℝ) ∧
    tf71P10 θ (49/1000) (153/500 : ℝ) = (947898039746/6098048325 : ℝ) ∧
    tf71P01 θ (49/1000) (153/500 : ℝ) = (88827082580400390625/118995818796912978 : ℝ) ∧
    tf71P11 θ (49/1000) (153/500 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_056_0866 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (4053597259559/1000000000000 : ℝ) ≤ tf71Ec θ (49/1000 : ℝ) (-14/25 : ℝ))
    (hE1hi : tf71Ec θ (49/1000 : ℝ) (-14/25 : ℝ) ≤ (101339931489/25000000000 : ℝ))
    (hE2lo : (100000000000/214853023407 : ℝ) ≤ tf71Ec θ (49/1000 : ℝ) (153/500 : ℝ))
    (hE2hi : tf71Ec θ (49/1000 : ℝ) (153/500 : ℝ) ≤ (1000000000000/2148530234069 : ℝ))
    :
    ((21/25 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (49/1000 : ℝ) (-14/25 : ℝ) - tf71Fr θ (49/1000 : ℝ) (153/500 : ℝ))
      - 2 * (21/25 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (49/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((2319/2500 : ℝ) + ((6957/1250 : ℝ)) * (1/1000000 : ℝ) + ((1507/1250 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((49/1000 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-14/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_056_0866 θ htan
  have hz2 : ((153/500 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_056_0866 θ htan
  have hΦ1 : tf71Fr θ (49/1000 : ℝ) (-14/25 : ℝ) ≤ (16199697257059/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (49/1000 : ℝ) (-14/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (1149276628607/1250000000 : ℝ) ≤ tf71Fr θ (49/1000 : ℝ) (153/500 : ℝ) := by
    rw [tf71Fr_bilinear θ (49/1000 : ℝ) (153/500 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (49/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (339850082192402676349/312500000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_058_084 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (1/20) (-29/50 : ℝ) = (326411450885135/606499127522 : ℝ) ∧
    tf71P10 θ (1/20) (-29/50 : ℝ) = (-671022546/2753405 : ℝ) ∧
    tf71P01 θ (1/20) (-29/50 : ℝ) = (214652587890625/606499127522 : ℝ) ∧
    tf71P11 θ (1/20) (-29/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_058_084 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (1/20) (13/50 : ℝ) = (27673938424055/89814239138 : ℝ) ∧
    tf71P10 θ (1/20) (13/50 : ℝ) = (142658514/1059565 : ℝ) ∧
    tf71P01 θ (1/20) (13/50 : ℝ) = (73435791015625/89814239138 : ℝ) ∧
    tf71P11 θ (1/20) (13/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_058_084 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (1034899591011/250000000000 : ℝ) ≤ tf71Ec θ (1/20 : ℝ) (-29/50 : ℝ))
    (hE1hi : tf71Ec θ (1/20 : ℝ) (-29/50 : ℝ) ≤ (827919672809/200000000000 : ℝ))
    (hE2lo : (1000000000000/1890459910019 : ℝ) ≤ tf71Ec θ (1/20 : ℝ) (13/50 : ℝ))
    (hE2hi : tf71Ec θ (1/20 : ℝ) (13/50 : ℝ) ≤ (500000000000/945229955009 : ℝ))
    :
    ((421/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (1/20 : ℝ) (-29/50 : ℝ) - tf71Fr θ (1/20 : ℝ) (13/50 : ℝ))
      - 2 * (421/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((464747/500000 : ℝ) + ((1394241/250000 : ℝ)) * (1/1000000 : ℝ) + ((302241/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((1/20 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-29/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_058_084 θ htan
  have hz2 : ((13/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_058_084 θ htan
  have hΦ1 : tf71Fr θ (1/20 : ℝ) (-29/50 : ℝ) ≤ (3260417704887/2000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (1/20 : ℝ) (-29/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (2366851301621/2500000000 : ℝ) ≤ tf71Fr θ (1/20 : ℝ) (13/50 : ℝ) := by
    rw [tf71Fr_bilinear θ (1/20 : ℝ) (13/50 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (6935715963110258701/6250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_06_0816 (θ : ℝ) (htan : Real.tan θ = 15/1) :
    tf71P00 θ (41/500) (-3/5 : ℝ) = (41396273818567/194875245000 : ℝ) ∧
    tf71P10 θ (41/500) (-3/5 : ℝ) = (-219052873/2341125 : ℝ) ∧
    tf71P01 θ (41/500) (-3/5 : ℝ) = (21419700721433/194875245000 : ℝ) ∧
    tf71P11 θ (41/500) (-3/5 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_06_0816 (θ : ℝ) (htan : Real.tan θ = 15/1) :
    tf71P00 θ (41/500) (27/125 : ℝ) = (86133297345703/10944967127112 : ℝ) ∧
    tf71P10 θ (41/500) (27/125 : ℝ) = (879199777/17545005 : ℝ) ∧
    tf71P01 θ (41/500) (27/125 : ℝ) = (4430639597245625/10944967127112 : ℝ) ∧
    tf71P11 θ (41/500) (27/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_06_0816 {θ : ℝ}
    (h1 : (150422816301907/100000000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (37605704075477/25000000000000 : ℝ))
    (htan : Real.tan θ = 15/1)
    (hE1lo : (4338547745397/1000000000000 : ℝ) ≤ tf71Ec θ (41/500 : ℝ) (-3/5 : ℝ))
    (hE1hi : tf71Ec θ (41/500 : ℝ) (-3/5 : ℝ) ≤ (2169273872699/500000000000 : ℝ))
    (hE2lo : (100000000000/169607079977 : ℝ) ≤ tf71Ec θ (41/500 : ℝ) (27/125 : ℝ))
    (hE2hi : tf71Ec θ (41/500 : ℝ) (27/125 : ℝ) ≤ (1000000000000/1696070799769 : ℝ))
    :
    ((211/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (41/500 : ℝ) (-3/5 : ℝ) - tf71Fr θ (41/500 : ℝ) (27/125 : ℝ))
      - 2 * (211/250 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (41/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((349271/375000 : ℝ) + ((349271/62500 : ℝ)) * (1/1000000 : ℝ) + ((75771/62500 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((41/500 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-3/5 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_06_0816 θ htan
  have hz2 : ((27/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_06_0816 θ htan
  have hΦ1 : tf71Fr θ (41/500 : ℝ) (-3/5 : ℝ) ≤ (5485490484317/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (41/500 : ℝ) (-3/5 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (804809507069/2500000000 : ℝ) ≤ tf71Fr θ (41/500 : ℝ) (27/125 : ℝ) := by
    rw [tf71Fr_bilinear θ (41/500 : ℝ) (27/125 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (12863344934231719511546343860777/35156250000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (41/500 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (2875973562652013879/7812500000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_062_0792 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (1/20) (-31/50 : ℝ) = (372651258880615/728518649042 : ℝ) ∧
    tf71P10 θ (1/20) (-31/50 : ℝ) = (-765373266/3017695 : ℝ) ∧
    tf71P01 θ (1/20) (-31/50 : ℝ) = (248275634765625/728518649042 : ℝ) ∧
    tf71P11 θ (1/20) (-31/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_062_0792 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (1/20) (43/250 : ℝ) = (108183578341602775/585839809398818 : ℝ) ∧
    tf71P10 θ (1/20) (43/250 : ℝ) = (1698318594/17114903 : ℝ) ∧
    tf71P01 θ (1/20) (43/250 : ℝ) = (588451080322265625/585839809398818 : ℝ) ∧
    tf71P11 θ (1/20) (43/250 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_062_0792 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (4565696601419/1000000000000 : ℝ) ≤ tf71Ec θ (1/20 : ℝ) (-31/50 : ℝ))
    (hE1hi : tf71Ec θ (1/20 : ℝ) (-31/50 : ℝ) ≤ (228284830071/50000000000 : ℝ))
    (hE2lo : (1000000000000/1523912459647 : ℝ) ≤ tf71Ec θ (1/20 : ℝ) (43/250 : ℝ))
    (hE2hi : tf71Ec θ (1/20 : ℝ) (43/250 : ℝ) ≤ (500000000000/761956229823 : ℝ))
    :
    ((847/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (1/20 : ℝ) (-31/50 : ℝ) - tf71Fr θ (1/20 : ℝ) (43/250 : ℝ))
      - 2 * (847/1000 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((5605409/6000000 : ℝ) + ((5605409/1000000 : ℝ)) * (1/1000000 : ℝ) + ((1217409/1000000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((1/20 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-31/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_062_0792 θ htan
  have hz2 : ((43/250 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_062_0792 θ htan
  have hΦ1 : tf71Fr θ (1/20 : ℝ) (-31/50 : ℝ) ≤ (16792276269677/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (1/20 : ℝ) (-31/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (9956983208373/10000000000 : ℝ) ≤ tf71Fr θ (1/20 : ℝ) (43/250 : ℝ) := by
    rw [tf71Fr_bilinear θ (1/20 : ℝ) (43/250 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (1/20 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (6935715963110258701/6250000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_064_077 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (51/1000) (-16/25 : ℝ) = (137536425218043027/271459339509760 : ℝ) ∧
    tf71P10 θ (51/1000) (-16/25 : ℝ) = (-83160860763/325636000 : ℝ) ∧
    tf71P01 θ (51/1000) (-16/25 : ℝ) = (18365199067146825/54291867901952 : ℝ) ∧
    tf71P11 θ (51/1000) (-16/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_064_077 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (51/1000) (13/100 : ℝ) = (183223433674611/7295090167690 : ℝ) ∧
    tf71P10 θ (51/1000) (13/100 : ℝ) = (8852728614/106764125 : ℝ) ∧
    tf71P01 θ (51/1000) (13/100 : ℝ) = (1734291918444825/1459018033538 : ℝ) ∧
    tf71P11 θ (51/1000) (13/100 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_064_077 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (1162446092059/250000000000 : ℝ) ≤ tf71Ec θ (51/1000 : ℝ) (-16/25 : ℝ))
    (hE1hi : tf71Ec θ (51/1000 : ℝ) (-16/25 : ℝ) ≤ (4649784368237/1000000000000 : ℝ))
    (hE2lo : (200000000000/273276499391 : ℝ) ≤ tf71Ec θ (51/1000 : ℝ) (13/100 : ℝ))
    (hE2hi : tf71Ec θ (51/1000 : ℝ) (13/100 : ℝ) ≤ (500000000000/683191248477 : ℝ))
    :
    ((849/1000 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (51/1000 : ℝ) (-16/25 : ℝ) - tf71Fr θ (51/1000 : ℝ) (13/100 : ℝ))
      - 2 * (849/1000 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (51/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((1872267/2000000 : ℝ) + ((5616801/1000000 : ℝ)) * (1/1000000 : ℝ) + ((1220801/1000000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((51/1000 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-16/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_064_077 θ htan
  have hz2 : ((13/100 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_064_077 θ htan
  have hΦ1 : tf71Fr θ (51/1000 : ℝ) (-16/25 : ℝ) ≤ (8442944173887/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (51/1000 : ℝ) (-16/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (5109945516429/5000000000 : ℝ) ≤ tf71Fr θ (51/1000 : ℝ) (13/100 : ℝ) := by
    rw [tf71Fr_bilinear θ (51/1000 : ℝ) (13/100 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (51/1000 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (353721514118623193751/312500000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_066_0748 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (-33/50 : ℝ) = (19297172592113/38439788805 : ℝ) ∧
    tf71P10 θ (13/250) (-33/50 : ℝ) = (-2817139598/10960125 : ℝ) ∧
    tf71P01 θ (13/250) (-33/50 : ℝ) = (2581754458400/7687957761 : ℝ) ∧
    tf71P11 θ (13/250) (-33/50 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_066_0748 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (11/125 : ℝ) = (-920396158676449/2724707011202 : ℝ) ∧
    tf71P10 θ (13/250) (11/125 : ℝ) = (2096356938/29179975 : ℝ) ∧
    tf71P01 θ (13/250) (11/125 : ℝ) = (4277734931640625/2724707011202 : ℝ) ∧
    tf71P11 θ (13/250) (11/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_066_0748 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (4732098115089/1000000000000 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (-33/50 : ℝ))
    (hE1hi : tf71Ec θ (13/250 : ℝ) (-33/50 : ℝ) ≤ (473209811509/100000000000 : ℝ))
    (hE2lo : (1000000000000/1230289069187 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (11/125 : ℝ))
    (hE2hi : tf71Ec θ (13/250 : ℝ) (11/125 : ℝ) ≤ (500000000000/615144534593 : ℝ))
    :
    ((213/250 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) (-33/50 : ℝ) - tf71Fr θ (13/250 : ℝ) (11/125 : ℝ))
      - 2 * (213/250 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((117373/125000 : ℝ) + ((352119/62500 : ℝ)) * (1/1000000 : ℝ) + ((76619/62500 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((13/250 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-33/50 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_066_0748 θ htan
  have hz2 : ((11/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_066_0748 θ htan
  have hΦ1 : tf71Fr θ (13/250 : ℝ) (-33/50 : ℝ) ≤ (16976597554613/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (-33/50 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (10482875299991/10000000000 : ℝ) ≤ tf71Fr θ (13/250 : ℝ) (11/125 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (11/125 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (90164307520433363113/78125000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_068_0728 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (-17/25 : ℝ) = (40977664656643/83680415290 : ℝ) ∧
    tf71P10 θ (13/250) (-17/25 : ℝ) = (-2988346842/11434625 : ℝ) ∧
    tf71P01 θ (13/250) (-17/25 : ℝ) = (5508800696425/16736083058 : ℝ) ∧
    tf71P11 θ (13/250) (-17/25 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_068_0728 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (6/125 : ℝ) = (-1180530016657849/805469857992 : ℝ) ∧
    tf71P10 θ (13/250) (6/125 : ℝ) = (613772029/7932675 : ℝ) ∧
    tf71P01 θ (13/250) (6/125 : ℝ) = (2182517822265625/805469857992 : ℝ) ∧
    tf71P11 θ (13/250) (6/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_068_0728 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (4960322513483/1000000000000 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (-17/25 : ℝ))
    (hE1hi : tf71Ec θ (13/250 : ℝ) (-17/25 : ℝ) ≤ (1240080628371/250000000000 : ℝ))
    (hE2lo : (500000000000/559841155921 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (6/125 : ℝ))
    (hE2hi : tf71Ec θ (13/250 : ℝ) (6/125 : ℝ) ≤ (1000000000000/1119682311841 : ℝ))
    :
    ((427/500 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) (-17/25 : ℝ) - tf71Fr θ (13/250 : ℝ) (6/125 : ℝ))
      - 2 * (427/500 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((470443/500000 : ℝ) + ((1411329/250000 : ℝ)) * (1/1000000 : ℝ) + ((307329/250000 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((13/250 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-17/25 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_068_0728 θ htan
  have hz2 : ((6/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_068_0728 θ htan
  have hΦ1 : tf71Fr θ (13/250 : ℝ) (-17/25 : ℝ) ≤ (8611755039553/5000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (-17/25 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (1072792600171/1000000000 : ℝ) ≤ tf71Fr θ (13/250 : ℝ) (6/125 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (6/125 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (90164307520433363113/78125000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_07_0708 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (-7/10 : ℝ) = (173775967079/363855625 : ℝ) ∧
    tf71P10 θ (13/250) (-7/10 : ℝ) = (-25317318/95375 : ℝ) ∧
    tf71P01 θ (13/250) (-7/10 : ℝ) = (117305339346/363855625 : ℝ) ∧
    tf71P11 θ (13/250) (-7/10 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem coefB_07_0708 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (1/125 : ℝ) = (-757787379806249/22314971282 : ℝ) ∧
    tf71P10 θ (13/250) (1/125 : ℝ) = (869797578/2640725 : ℝ) ∧
    tf71P01 θ (13/250) (1/125 : ℝ) = (785706416015625/22314971282 : ℝ) ∧
    tf71P11 θ (13/250) (1/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_07_0708 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (2599776974119/500000000000 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (-7/10 : ℝ))
    (hE1hi : tf71Ec θ (13/250 : ℝ) (-7/10 : ℝ) ≤ (5199553948239/1000000000000 : ℝ))
    (hE2lo : (25000000000/25475486023 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (1/125 : ℝ))
    (hE2hi : tf71Ec θ (13/250 : ℝ) (1/125 : ℝ) ≤ (1000000000000/1019019440919 : ℝ))
    :
    ((107/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) (-7/10 : ℝ) - tf71Fr θ (13/250 : ℝ) (1/125 : ℝ))
      - 2 * (107/125 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((176773/187500 : ℝ) + ((176773/31250 : ℝ)) * (1/1000000 : ℝ) + ((38523/31250 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((13/250 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-7/10 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_07_0708 θ htan
  have hz2 : ((1/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hd00,hd10,hd01,hd11⟩ := coefB_07_0708 θ htan
  have hΦ1 : tf71Fr θ (13/250 : ℝ) (-7/10 : ℝ) ≤ (17475516997509/10000000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (-7/10 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hΦ2 : (34318144279/31250000 : ℝ) ≤ tf71Fr θ (13/250 : ℝ) (1/125 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (1/125 : ℝ) hθ0 hθπ hlam hz2, hd00, hd10, hd01, hd11]
    linarith only [h1, h2, hE2lo]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (90164307520433363113/78125000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hΦ2, hF0, hf0]

theorem coefA_0704_0704 (θ : ℝ) (htan : Real.tan θ = 25/1) :
    tf71P00 θ (13/250) (-88/125 : ℝ) = (137335435415840207/289003496617088 : ℝ) ∧
    tf71P10 θ (13/250) (-88/125 : ℝ) = (-40006770141/150261100 : ℝ) ∧
    tf71P01 θ (13/250) (-88/125 : ℝ) = (92779705631640625/289003496617088 : ℝ) ∧
    tf71P11 θ (13/250) (-88/125 : ℝ) = (0/1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tf71P00, tf71P10, tf71P01, tf71P11, tf71Jc0, tf71JcE, tf71Js0, tf71JsE,
      tf71KcTE, tf71KcE, tf71Dc, tf71Bcf, tf71s2, tf71c2, htan]
    norm_num

theorem rowcert_0704_0704 {θ : ℝ}
    (h1 : (3827044099179/2500000000000 : ℝ) ≤ θ)
    (h2 : θ ≤ (153081763967161/100000000000000 : ℝ))
    (htan : Real.tan θ = 25/1)
    (hE1lo : (5248767352139/1000000000000 : ℝ) ≤ tf71Ec θ (13/250 : ℝ) (-88/125 : ℝ))
    (hE1hi : tf71Ec θ (13/250 : ℝ) (-88/125 : ℝ) ≤ (262438367607/50000000000 : ℝ))
    :
    ((107/125 : ℝ) ^ 2 + 1/2) * (tf71Fr θ (13/250 : ℝ) (-88/125 : ℝ) - 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      - 2 * (107/125 : ℝ) * (2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2)
      + (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3)
          * ((176773/187500 : ℝ) + ((176773/31250 : ℝ)) * (1/1000000 : ℝ) + ((38523/31250 : ℝ)) * (1/1000000 : ℝ)) < 0 := by
  have hθ0 : 0 < θ := by linarith only [h1]
  have hθπ : θ < Real.pi / 2 := by linarith only [Real.pi_gt_d4, h2]
  have hlam : ((13/250 : ℝ)) ≠ 0 := by norm_num
  have hz1 : ((-88/125 : ℝ)) ≠ 0 := by norm_num
  obtain ⟨hc00,hc10,hc01,hc11⟩ := coefA_0704_0704 θ htan
  have hΦ1 : tf71Fr θ (13/250 : ℝ) (-88/125 : ℝ) ≤ (2190817579401/1250000000 : ℝ) := by
    rw [tf71Fr_bilinear θ (13/250 : ℝ) (-88/125 : ℝ) hθ0 hθπ hlam hz1, hc00, hc10, hc01, hc11]
    linarith only [h1, h2, hE1hi]
  have hF0 : (1724011889673153181266292043175273/1562500000000000000000000000000 : ℝ) ≤ 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
    rw [htan]; nlinarith only [h1, h2]
  have hf0 : (13/250 : ℝ) * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ / Real.tan θ - 3) ≤ (90164307520433363113/78125000000000000 : ℝ) := by
    rw [htan]; linarith only [h1, h2]
  linarith only [hΦ1, hF0, hf0]

end Work.ZeroFreeTables
